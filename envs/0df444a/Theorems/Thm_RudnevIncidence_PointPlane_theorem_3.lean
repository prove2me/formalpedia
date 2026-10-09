-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_theorem_3
-- name    : RudnevIncidence.PointPlane.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:47.030832+00:00
-- url     : https://prove2.me/theorems/cae11139-9567-41a1-95ef-0e1b3fdee92e
-- title:
--   Theorem 3 — m points and n ≤ m planes in P³ (char ≠ 2, n = O(p²)) have O(m√n + km) incidences, k the maximum number of collinear planes
-- statement:
--   There are absolute constants $c>0$ and $C>0$ with the following property. Let $\mathbb F$ be a field, of characteristic $p\neq2$ if the characteristic is positive. Let $P$ be a set of $m$ points and $\Pi$ a set of $n$ planes of $\mathbb P^3$ over $\mathbb F$, with $m\ge n$, and, if $\mathbb F$ has positive characteristic $p$, $n\le cp^2$. Let $k$ be the maximum number of planes of $\Pi$ containing a common line. Then
--   $$|I(P,\Pi)|\le C\big(m\sqrt n+km\big).$$
--
--   This is estimate (5), the main result of the paper: a point–plane incidence bound valid over every field, including fields of positive characteristic, with the collinearity parameter $k$ accounting for the trivial configurations in which many planes share a line. Its main term cannot be improved in positive characteristic under the constraint $\min(m,n)=O(p^2)$ alone (Remark 4).
--
--   **Formalization Note** "$n=O(p^2)$" is read as $n\le cp^2$ with an absolute, existentially quantified $c>0$ — the reading Theorem 12 states explicitly ("Let $n\le cp^2$, for some absolute $c$"); it applies only in positive characteristic. Both constants come before the field and the configuration, because the paper declares $O(\cdot)$ and $c$ absolute (p. 1). $k$ is any upper bound on the number of planes of $\Pi$ through a line of $\mathbb P^3$; this is equivalent to the maximum because the right-hand side is monotone in $k$, and it avoids a supremum over infinitely many lines. Points and planes are elements of the projectivisation of $\mathbb F^4$, so the sets contain distinct projective objects. $\mathbb F$ ranges over fields in the universe `Type`.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 4, Theorem 3, (5)

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type) [Field F], ringChar F ≠ 2 →
      ∀ (P Pl : Finset (ℙ F (Fin 4 → F))) (k : ℕ),
        Pl.card ≤ P.card →
        (ringChar F ≠ 0 → (Pl.card : ℝ) ≤ c * (ringChar F : ℝ) ^ 2) →
        (∀ W : Submodule F (Fin 4 → F), Module.finrank F W = 2 → (planesThrough Pl W).card ≤ k) →
        (incidences P Pl : ℝ) ≤
          C * ((P.card : ℝ) * Real.sqrt (Pl.card : ℝ) + (k : ℝ) * (P.card : ℝ)) := by sorry
end RudnevIncidence.PointPlane
