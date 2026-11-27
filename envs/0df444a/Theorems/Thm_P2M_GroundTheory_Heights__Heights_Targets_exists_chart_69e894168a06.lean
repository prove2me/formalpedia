-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_exists_chart_69e894168a06
-- name    : P2M_GroundTheory_Heights__Heights_Targets_exists_chart_69e894168a06
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:42.611348+00:00
-- url     : https://prove2.me/theorems/a74d32aa-a2d2-4c9c-8d37-7cb0492d7b4d
-- title:
--   P2 M Ground Theory Heights  Heights Targets exists chart 69e894168a06: P2 M Ground Theory Heights  Heights Targets exists chart 69e894168a06
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets exists chart 69e894168a06 construction uses the P2 M Ground Theory Heights  Heights Targets exists chart 69e894168a06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L94-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Targets_exists_chart_69e894168a06 {y : (Σ k, ι k) → Ω} {n : ℕ} (hP : IsArithVar (mCoordIdeal y) n) :
    ∃ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«exists_chart» := P2M_GroundTheory_Heights__Heights_Targets_exists_chart_69e894168a06
