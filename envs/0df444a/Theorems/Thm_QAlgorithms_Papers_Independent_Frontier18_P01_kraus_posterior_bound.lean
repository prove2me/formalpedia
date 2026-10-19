-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_kraus_posterior_bound
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.kraus_posterior_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:50:41.681769+00:00
-- url     : https://prove2.me/theorems/b7546961-8d27-4168-a42b-e7dc06679280
-- title:
--   Proposition 3: Kraus posterior-entropy upper bound and equality case
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\{V_i\}_{i\ge1}$ be a countable Kraus family with $\sum_iV_i^*V_i=\mathbf1$ strongly, and write $\Phi(X)=\sum_iV_iXV_i^*$. For $H(\rho)<\infty$, put $p_i=\operatorname{Tr}(V_i\rho V_i^*)$. Then
--
--   $$I_c(\rho,\Phi)\le\sum_iH(V_i\rho V_i^*)=\sum_i p_iH\!\left(\frac{V_i\rho V_i^*}{p_i}\right).$$
--
--   The entropy on positive operators is homogeneous, and the entire term at $p_i=0$ is defined to be zero. If the ranges of distinct Kraus operators are orthogonal, the upper bound is attained. Orthogonality is only a sufficient condition.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 18, Proposition 3: Kraus posterior-entropy upper bound and equality case

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Proposition 3, equation (27), PDF pp.18–19. The two sums always agree;
orthogonal ranges are sufficient for saturation, not necessary. -/
theorem kraus_posterior_bound [Countable I] [Countable J] (rho : State I) (V : KrausFamily I J)
    (hin : homogeneousEntropy rho.coefficients < ⊤) :
    (finiteInputCoherentInfo rho.coefficients (countableKrausAction V) : EReal) ≤
      (posteriorEntropy rho.coefficients V).toEReal ∧
    posteriorEntropy rho.coefficients V = normalizedPosteriorEntropy rho.coefficients V ∧
    (OrthogonalRanges V → (finiteInputCoherentInfo rho.coefficients (countableKrausAction V) : EReal) =
      (posteriorEntropy rho.coefficients V).toEReal) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
