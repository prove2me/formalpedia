-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_order_regularity
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.order_regularity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:29:52.750994+00:00
-- url     : https://prove2.me/theorems/fbb44c25-7e61-43f0-9931-594bb550ce68
-- title:
--   Corollary 10: Continuity, monotonicity and scaled convexity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. For states $\rho_{AB},\tau_A$ with $\rho_A\ll\tau_A$, set $F(\alpha)=\widetilde I_\alpha(\rho\|\tau)$. Then
--   $$F\text{ is continuous and nondecreasing on }[1/2,\infty),\qquad t\mapsto tF(1+t)\text{ is continuous and convex on }[-1/2,\infty).$$
--   Continuity at the left endpoints is relative to the displayed domains. These regularity properties support the variational exponent formulas without asserting endpoint differentiability.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 11, Corollary 10: Continuity, monotonicity and scaled convexity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.11, Corollary 10. Continuity at 1/2 is relativeEntropy
to the domain; this makes no endpoint differentiability assertion. -/
theorem order_regularity [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) :
    ContinuousOn (fun a : ℝ => (generalizedInformation true (a : RenyiOrder) rho tau).toReal) (Set.Ici (1/2 : ℝ)) ∧
    MonotoneOn (fun a : ℝ => (generalizedInformation true (a : RenyiOrder) rho tau).toReal) (Set.Ici (1/2 : ℝ)) ∧
    ContinuousOn (fun t : ℝ => t * (generalizedInformation true ((1+t : ℝ) : RenyiOrder) rho tau).toReal) (Set.Ici (-1/2 : ℝ)) ∧
    ConvexOn ℝ (Set.Ici (-1/2 : ℝ)) (fun t : ℝ => t * (generalizedInformation true ((1+t : ℝ) : RenyiOrder) rho tau).toReal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
