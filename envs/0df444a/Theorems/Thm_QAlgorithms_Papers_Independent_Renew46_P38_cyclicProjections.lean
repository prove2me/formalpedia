-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_cyclicProjections
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.cyclicProjections
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:11:50.241567+00:00
-- url     : https://prove2.me/theorems/b94514a4-ca25-44c1-918c-21435ed2a2b7
-- title:
--   Orthogonal cyclic translates of the uniform rank-one projection
-- statement:
--   Let $n\geq1$ and define scalar complex $n\times n$ matrices $P$ and $E$ by $P_{ij}=1/n$ and $E=\operatorname{diag}(\theta,\theta^2,\ldots,\theta^n)$, where $\theta=\exp(2\pi i/n)$. The matrix $P$ is the rank-one orthogonal projection onto the span of the sum of the standard basis vectors. Define $P_k=E^{-k}PE^k$ for $1\leq k\leq n$. Then every $P_k$ is a rank-one orthogonal projection, and
--   $$P_kP_l=0\quad(k\ne l),\qquad \sum_{k=1}^nP_k=1.$$
--   These rank claims concern the scalar matrices. Their amplification on $H^n$ would instead have rank $\dim H$. The matrices are defined from $n$ rather than supplied as objects satisfying these conclusions.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 6, Corollary 3.2: cyclic translates of the uniform rank-one projection

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Corollary 3.2, PDF p. 6.
Rank one is asserted only for the scalar matrices, not their amplification on H^n. -/
theorem cyclicProjections (n : ℕ) (hn : 1 ≤ n) :
    IsStarProjection (uniformProjection n) ∧ (uniformProjection n).rank = 1 ∧
    (Set.range (Matrix.mulVec (uniformProjection n)) =
      (Submodule.span ℂ ({fun _ : Fin n => (1 : ℂ)} : Set (Fin n → ℂ)) :
        Set (Fin n → ℂ))) ∧
    (∀ k : Fin n, IsStarProjection (cyclicProjection n k) ∧ (cyclicProjection n k).rank = 1) ∧
    (∀ k l : Fin n, k ≠ l → cyclicProjection n k * cyclicProjection n l = 0) ∧
    (∑ k : Fin n, cyclicProjection n k) = 1 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
