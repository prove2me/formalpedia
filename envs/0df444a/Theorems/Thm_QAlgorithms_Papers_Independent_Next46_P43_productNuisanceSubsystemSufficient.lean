-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_productNuisanceSubsystemSufficient
-- name    : QAlgorithms.Papers.Independent.Next46.P43.productNuisanceSubsystemSufficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:39:12.290925+00:00
-- url     : https://prove2.me/theorems/8b9fa86d-6c7f-4b06-96de-3152360414e9
-- title:
--   Example 3: product nuisance subsystem is sufficient
-- statement:
--   Let $H_L,H_R,H_B$ be separable complex Hilbert spaces, let $\Theta$ be nonempty, and let $\rho_\theta^L$ and $\tau^{RB}$ be normal states, the latter independent of $\theta$. Suppose the normal state $\rho_\theta$ on $H_L\otimes(H_R\otimes H_B)$ has density $D_\theta=D_\theta^L\otimes D^{RB}$. Then the restriction to $B(H_L)$ is sufficient, and
--
--   $$
--   \mathcal R(\operatorname{Tr}_{RB}D_\theta)=D_\theta,
--   \qquad \mathcal R(X)=X\otimes D^{RB}.
--   $$
--
--   There is one normal-predual trace-preserving 2-positive reverse map for the whole family. The fixed attachment displayed above recovers each state. No injectivity of the parameterization is assumed. This describes a subsystem carrying all statistical information despite an arbitrary fixed nuisance subsystem.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 5, Example 3: product nuisance subsystem is sufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Example 3, PDF p.5. A fixed normal nuisance state on R tensor B is
attached to every L marginal. The L restriction is sufficient in arbitrary
separable Hilbert spaces, and the explicit fixed-state attachment recovers
the original density. This asserts state recovery, without assuming the
parameterization is injective or asserting identifiability of theta. -/
theorem productNuisanceSubsystemSufficient
    {I J K Theta : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty Theta] (left : Theta → State I) (nuisance : State (J × K))
    (phi : Theta → State (I × (J × K)))
    (hProduct : ∀ theta, (phi theta).coefficients =
      productCoeff (left theta).coefficients nuisance.coefficients) :
    SufficientTraceClassMap (traceSecond (I := I) (J := J × K))
      (fun theta => (phi theta).coefficients) ∧
    ∀ theta, productCoeff (traceSecond (phi theta).coefficients)
      nuisance.coefficients = (phi theta).coefficients := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
