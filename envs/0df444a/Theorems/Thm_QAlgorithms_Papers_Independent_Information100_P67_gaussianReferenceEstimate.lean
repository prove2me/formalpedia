-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_gaussianReferenceEstimate
-- name    : QAlgorithms.Papers.Independent.Information100.P67.gaussianReferenceEstimate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:56:36.204088+00:00
-- url     : https://prove2.me/theorems/743cc85c-066f-4824-880d-ee9b56a0846a
-- title:
--   Unnumbered filter ingredient: Gaussian reference estimate (5.7)
-- statement:
--   Let $\tau_{AR}\ge0$ have trace at most one. Let $\sigma_R$ be a normalized density matrix, $\lambda>0$, and assume $\tau_{AR}\le\lambda I_A\otimes\sigma_R$. For any integer $L\ge1$, choose $Z:A\to\mathbb C^L$ with entries $Z_{ai}=(\xi_{ai}+i\eta_{ai})/\sqrt{2L}$, where all real coordinates are independent standard Gaussians under their finite product probability measure. Put $\tau_R^Z=\operatorname{Tr}_C[(Z\otimes I_R)\tau(Z^\dagger\otimes I_R)]$ and $\tau_R=\operatorname{Tr}_A\tau$. The displayed random variable is integrable and
--
--   $$\mathbb E\,\|\tau_R^Z-\tau_R\|_1\le\sqrt{\lambda/L}.$$
--
--   The estimate imposes no invertibility assumption on $\sigma_R$ and is independent of its smallest positive eigenvalue and of $\dim R$.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 24, Unnumbered filter ingredient: Gaussian reference estimate (5.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Gaussian reference estimate (5.7), PDF pp.24–26. Integrability is part
of the conclusion, so the expectation cannot use a default Bochner zero. -/
theorem gaussianReferenceEstimate [Nonempty A] [Nonempty R]
    (tau : Matrix (A × R) (A × R) ℂ) (htau : IsSubnormalized tau)
    (sigma : Matrix R R ℂ) (hsigma : IsDensityMatrix sigma)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hdom : ((lambda : ℂ) • Matrix.kronecker (1 : Matrix A A ℂ) sigma - tau).PosSemidef)
    (L : ℕ) (hL : 0 < L) :
    let integrand := fun z : (Fin L × (A × Bool)) → ℝ =>
      traceNorm (referenceFilterMap (gaussianFilter L z) tau - traceLeft tau)
    Integrable integrand (gaussianFilterLaw L A) ∧
      (∫ z, integrand z ∂gaussianFilterLaw L A) ≤ Real.sqrt (lambda / L) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
