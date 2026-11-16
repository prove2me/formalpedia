-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_lemma_8_4
-- name    : UPPIntersection.Halfspaces.Supplement.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:53.455245+00:00
-- url     : https://prove2.me/theorems/d75ddbf2-1b29-41ef-9772-2688c8e9488a
-- title:
--   Lemma 8.4 — $\mathrm{rank}_\pm(\wedge^kA)\le\binom{kd+D}{D}$ for sign matrices of finite sets with margin $\eta$
-- statement:
--   There is a universal constant $K>0$ with the following property. Let $\eta\in(0,1/2)$ and $k\ge1$; then there is $D\le Kk^2\log(1/\eta)$, i.e. $D=O(k^2\log(1/\eta))$, such that for every dimension $d$ and all finite sets $A,B\subseteq\mathbb R^d$ with $\eta\le|\langle a,b\rangle|\le1$ for all $a\in A$, $b\in B$, the sign matrix $A\in\{-1,1\}^{A\times B}$ defined by $A_{a,b}=\operatorname{sgn}\langle a,b\rangle$ satisfies
--   $$\operatorname{rank}_\pm\big(\wedge^kA\big)\le\binom{kd+D}{D}.$$
--   Here $\wedge^kA$ has rows $(a_1,\dots,a_k)\in A^k$, columns $(b_1,\dots,b_k)\in B^k$ and entry $A_{a_1,b_1}\wedge\cdots\wedge A_{a_k,b_k}$, and $\log$ is base 2.
--
--   This is the general upper bound behind the tightness results Theorem 8.5 (integer halfspaces) and Theorem 8.6 (random points).
--
--   Differences from the source:
--   - reading: for D = O(k² log(1/η)) → one D ≤ K k² log₂(1/η), with K universal and D chosen before d, A and B; reason: the source does not say whether D may depend on d, A, B; the stronger reading, D independent of them, is taken, and it is the one the proof gives (D is the degree from Lemma 8.3, which depends only on k and η)
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 32, Lemma 8.4 (proof on p. 32); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_Supplement_Defs

open SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Lemma 8.4 (p. 32). There is a universal constant `K > 0` such that for every
`η ∈ (0, 1/2)` and `k ≥ 1` there is a `D ≤ K k² log₂(1/η)` (i.e. `D = O(k² log(1/η))`) with the
following property: for every dimension `d` and all finite `A, B ⊆ ℝ^d` with `η ≤ |⟨a,b⟩| ≤ 1` for
all `a ∈ A`, `b ∈ B`, the sign matrix `A_{a,b} = sgn⟨a,b⟩` satisfies
`rank_±(∧^k A) ≤ binom(kd + D, D)`. -/
theorem lemma_8_4 : ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 → ∀ k : ℕ, 1 ≤ k →
    ∃ D : ℕ, (D : ℝ) ≤ K * (k : ℝ) ^ 2 * Real.logb 2 (1 / η) ∧
      ∀ (d : ℕ) (A B : Finset (EuclideanSpace ℝ (Fin d))),
        (∀ a ∈ A, ∀ b ∈ B, η ≤ |inner ℝ a b| ∧ |inner ℝ a b| ≤ 1) →
        signRank (kfoldAnd k (finSignMat A B)) ≤ (k * d + D).choose D := by sorry

end UPPIntersection.Halfspaces.Supplement
