-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_curveChartMono_notMem_6e92c9cb1350
-- name    : P2M_GroundTheory_Heights__Heights_Targets_curveChartMono_notMem_6e92c9cb1350
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:33.567937+00:00
-- url     : https://prove2.me/theorems/7e0f77d8-781e-55dc-869c-960f48c322e2
-- title:
--   P2 M Ground Theory Heights  Heights Targets curve Chart Mono not Mem 6e92c9cb1350: P2 M Ground Theory Heights  Heights Targets curve Chart Mono not Mem 6e92c9cb1350
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets curve Chart Mono not Mem 6e92c9cb1350 construction uses the P2 M Ground Theory Heights  Heights Targets curve Chart Mono not Mem 6e92c9cb1350 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L85-L92

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_curveChartMono_notMem_6e92c9cb1350 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    curveChartMono c d ∉ mCoordIdeal y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«curveChartMono_notMem» := P2M_GroundTheory_Heights__Heights_Targets_curveChartMono_notMem_6e92c9cb1350
