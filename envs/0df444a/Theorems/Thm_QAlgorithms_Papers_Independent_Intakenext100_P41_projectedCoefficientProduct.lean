-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_projectedCoefficientProduct
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.projectedCoefficientProduct
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:35:31.135221+00:00
-- url     : https://prove2.me/theorems/2141bae6-fd26-416d-b36f-81df0ded5c98
-- title:
--   Projected Frobenius coefficients
-- statement:
--   For the basic ODE $f'=Pf/z+Qf/(1-z)$ with $Q=v\varphi$ under all §18 hypotheses, fix a normalized eigenvector $\xi_{i,0}$ of $P$ with eigenvalue $\lambda_i$. Construct its coefficients by
--
--   $$(\lambda_i+n-P)\xi_{i,n}=Q\sum_{r=0}^{n-1}\xi_{i,r}\quad(n\ge1),\qquad \alpha_{i,n}=\varphi\left(\sum_{r=0}^n\xi_{i,r}\right).$$
--
--   For every $n\ge0$, with $\chi_P(t)=1+\varphi((tI-P)^{-1}v)$,
--
--   $$\alpha_{i,n}=\varphi(\xi_{i,0})\prod_{m=1}^n\chi_P(\lambda_i+m).$$
--
--   The empty product is one, and nonresonance ensures that every inverse at positive $m$ exists. This retains displayed equation (5); the erroneous intervening prose recurrence is not used as a definition.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 28, §22: Let Q(ξ0 + · · · + ξn ) = αn v,

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §22 equation (5), PDF p.28. The printed intervening recurrence has an
index/factor typo. The directly preceding resolvent identity gives
α_n=χ_P(λ+n)α_{n−1}, yielding the printed product below, including n=0. -/
theorem projectedCoefficientProduct {d : ℕ} (A : BasicODEData d) (i : Fin d) (n : ℕ) :
    projectedCoefficient A i n = A.phi (A.xi i) *
      ∏ m ∈ Finset.range n,
        resolventScalar A.P A.v A.phi (A.lambda i + ((m + 1 : ℕ) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
