-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_isMultiHomog_curveChartMono_8c3e1926fba1
-- name    : P2M_GroundTheory_Heights__Heights_Targets_isMultiHomog_curveChartMono_8c3e1926fba1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:40:54.04534+00:00
-- url     : https://prove2.me/theorems/fcaee51b-2a07-4b4c-a309-3826105d6b07
-- title:
--   P2 M Ground Theory Heights  Heights Targets is Multi Homog curve Chart Mono 8c3e1926fba1: P2 M Ground Theory Heights  Heights Targets is Multi Homog curve Chart Mono 8c3e1926fba1
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets is Multi Homog curve Chart Mono 8c3e1926fba1 construction uses the P2 M Ground Theory Heights  Heights Targets is Multi Homog curve Chart Mono 8c3e1926fba1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L51-L66

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

theorem P2M_GroundTheory_Heights__Heights_Targets_isMultiHomog_curveChartMono_8c3e1926fba1 (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (curveChartMono c d) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«isMultiHomog_curveChartMono» := P2M_GroundTheory_Heights__Heights_Targets_isMultiHomog_curveChartMono_8c3e1926fba1
