-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_coeff_eq_zero_674c17c17c2e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_coeff_eq_zero_674c17c17c2e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:44.674649+00:00
-- url     : https://prove2.me/theorems/39b98766-3d8e-41a7-8e8d-022bfe4e18eb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep coeff eq zero 674c17c17c2e: P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep coeff eq zero 674c17c17c2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep coeff eq zero 674c17c17c2e construction uses the P2 M Ground Theory Heights  Heights Inter Chart Scaling Indep coeff eq zero 674c17c17c2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartScalingIndep.lean#L26-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartScalingIndep.lean#L26-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartScalingIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_coeff_eq_zero_674c17c17c2e (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k) (hx : ∀ k, x ⟨k, i k⟩ ≠ 0)
    (hV : IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)))
    (s : Finset (K →₀ ℕ)) (g : (K →₀ ℕ) → MRingOver F ι)
    (hs : ∑ α ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0) :
    ∀ β ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g β) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartScalingIndep».«coeff_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_coeff_eq_zero_674c17c17c2e
