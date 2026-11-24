-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_pow_mem_2f024e5dc2e9
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_pow_mem_2f024e5dc2e9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:08.174776+00:00
-- url     : https://prove2.me/theorems/40ee89bc-bbe4-419e-b1a4-b20edb35838f
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat pow mem 2f024e5dc2e9: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat pow mem 2f024e5dc2e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat pow mem 2f024e5dc2e9 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat pow mem 2f024e5dc2e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L51-L60

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
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_pow_mem_2f024e5dc2e9 {a : ℕ} {g : K'} (hg : g ∈ chartLat y 1 a) (n : ℕ) :
    g ^ n ∈ chartLat y 1 (a * n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«chartLat_pow_mem» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_pow_mem_2f024e5dc2e9
