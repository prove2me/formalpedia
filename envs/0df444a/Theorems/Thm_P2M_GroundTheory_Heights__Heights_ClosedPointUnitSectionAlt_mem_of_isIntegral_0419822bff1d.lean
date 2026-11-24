-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_isIntegral_0419822bff1d
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_isIntegral_0419822bff1d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:58.025808+00:00
-- url     : https://prove2.me/theorems/1a3c2a21-ee3d-4dff-8b92-ec56ed4fb624
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of is Integral 0419822bff1d: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of is Integral 0419822bff1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of is Integral 0419822bff1d construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of is Integral 0419822bff1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L309-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L309-L313

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
omit [Fintype T] [NumberField K']

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_isIntegral_0419822bff1d (W : ValuationSubring K') {x : K'} (hx : IsIntegral ℤ x) : x ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«mem_of_isIntegral» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_isIntegral_0419822bff1d
