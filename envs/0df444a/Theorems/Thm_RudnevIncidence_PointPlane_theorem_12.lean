-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_theorem_12
-- name    : RudnevIncidence.PointPlane.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:46.646177+00:00
-- url     : https://prove2.me/theorems/0d518650-cb98-4194-8bfe-9aaeef494df7
-- title:
--   Theorem 12, pp. 14–15 — two disjoint families of mutually skew lines in G = K ∩ S (S not tangent) have O(m√n + km) incidences
-- statement:
--   There are absolute constants $c>0$ and $C>0$ with the following property. Let $\mathbb F$ be an algebraically closed field of characteristic $p\neq2$, and let $S$ be a hyperplane of $\mathbb P^5$ not tangent to the Klein quadric $\mathcal K$, so that $\mathcal G=\mathcal K\cap S$ is a three-quadric in $S\cong\mathbb P^4$. Let $L_\alpha$, $L_\beta$ be two disjoint sets of $m$ and $n$ lines contained in $\mathcal G$, such that the lines within each family are mutually skew. Assume $m\ge n$, and $n\le cp^2$ if $p>0$. Let $k$ be the maximum number of lines of $L_\beta$ contained in the intersection of $\mathcal G$ with a projective three-subspace of $S$. Then
--   $$|I(L_\alpha,L_\beta)|\le C\big(m\sqrt n+km\big).$$
--
--   This is estimate (14). Together with Lemma 9, which converts a point–plane arrangement in $\mathbb P^3$ into such a pair of line families, it yields Theorem 3.
--
--   **Formalization Note** The constants $c$ and $C$ are quantified before the field and the families, because the paper declares $O(\cdot)$ and $c$ absolute (p. 1). The constraint $n\le cp^2$ is guarded by "positive characteristic"; in characteristic 0 there is none. $k$ is any upper bound on the number of $L_\beta$-lines in a three-subspace of $S$ (a 4-dimensional subspace $V\subseteq S$ of $\mathbb F^6$); this is equivalent to taking the maximum since the bound is monotone in $k$. Lines are 2-dimensional subspaces of $\mathbb F^6$, and two lines meet when they share a nonzero vector. $\mathbb F$ ranges over fields in the universe `Type`.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, pp. 14–15, Theorem 12, (14)

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem theorem_12 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F], ringChar F ≠ 2 →
      ∀ (U : Fin 6 → F), NonTangent U →
      ∀ (Lα Lβ : Finset (Submodule F (Fin 6 → F))) (k : ℕ),
        (∀ W ∈ Lα, IsLineIn U W) → (∀ W ∈ Lβ, IsLineIn U W) → Disjoint Lα Lβ →
        (Lα : Set (Submodule F (Fin 6 → F))).Pairwise (fun W W' => W ⊓ W' = ⊥) →
        (Lβ : Set (Submodule F (Fin 6 → F))).Pairwise (fun W W' => W ⊓ W' = ⊥) →
        Lβ.card ≤ Lα.card →
        (ringChar F ≠ 0 → (Lβ.card : ℝ) ≤ c * (ringChar F : ℝ) ^ 2) →
        (∀ V : Submodule F (Fin 6 → F), V ≤ hyperplane U → Module.finrank F V = 4 →
          (Lβ.filter (· ≤ V)).card ≤ k) →
        (lineIncidences Lα Lβ : ℝ) ≤
          C * ((Lα.card : ℝ) * Real.sqrt (Lβ.card : ℝ) + (k : ℝ) * (Lα.card : ℝ)) := by sorry
end RudnevIncidence.PointPlane
