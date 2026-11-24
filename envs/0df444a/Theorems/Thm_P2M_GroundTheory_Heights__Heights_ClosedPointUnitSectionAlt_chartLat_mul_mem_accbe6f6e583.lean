-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:33.358011+00:00
-- url     : https://prove2.me/theorems/1a301bed-ffe0-419b-91e8-8a7a5e56d439
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat mul mem accbe6f6e583: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat mul mem accbe6f6e583
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat mul mem accbe6f6e583 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt chart Lat mul mem accbe6f6e583 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L43-L48

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583 {a b : ℕ} {g h : K'} (hg : g ∈ chartLat y 1 a) (hh : h ∈ chartLat y 1 b) :
    g * h ∈ chartLat y 1 (a + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«chartLat_mul_mem» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583
