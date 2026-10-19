-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_relative_entropy_mixture_lower
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.relative_entropy_mixture_lower
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:59:44.661241+00:00
-- url     : https://prove2.me/theorems/bcbd346f-6cd4-48fe-ab75-04ae5ab57cc2
-- title:
--   Appendix Lemma 6: lower mixture bound for relative entropy
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\rho,\sigma$ be states and $C$ any positive trace-class operator, including zero. For $0\le t\le1$, set $h_2(t)=-t\log t-(1-t)\log(1-t)$ with the endpoint convention $0\log0=0$. Then
--
--   $$tD(\rho\Vert C)+(1-t)D(\sigma\Vert C)\le D(t\rho+(1-t)\sigma\Vert C)+h_2(t).$$
--
--   The inequality is in extended nonnegative reals with $0\cdot\infty=0$. This addition form is equivalent to the printed lower bound with finite $h_2(t)$ subtracted.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 24, Appendix Lemma 6: lower mixture bound for relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Appendix Lemma 6, PDF pp.24–25. Addition form is equivalent to subtracting
finite h_2 on the right, and covers endpoints and infinite relative entropies. -/
theorem relative_entropy_mixture_lower [Countable I] (rho sigma : State I) (C : Matrix I I ℂ)
    (hC : IsTraceClass C) (hpos : IsPositive C) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ENNReal.ofReal t * generalizedRelativeEntropy rho.coefficients C +
      ENNReal.ofReal (1-t) * generalizedRelativeEntropy sigma.coefficients C ≤
      generalizedRelativeEntropy (convexOperatorMixture t rho.coefficients sigma.coefficients) C + binaryEntropy t := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
