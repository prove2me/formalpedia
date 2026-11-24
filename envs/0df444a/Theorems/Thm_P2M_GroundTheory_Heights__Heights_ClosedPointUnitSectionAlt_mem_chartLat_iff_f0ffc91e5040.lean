-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:58.548746+00:00
-- url     : https://prove2.me/theorems/e28fa289-00c3-45a4-8733-b0e1d4571d8a
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem chart Lat iff f0ffc91e5040: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem chart Lat iff f0ffc91e5040
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem chart Lat iff f0ffc91e5040 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem chart Lat iff f0ffc91e5040 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L18-L31

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040 {d : ℕ} {g : K'} :
    g ∈ chartLat y 1 d ↔
      ∀ t : T, y ⟨(), t⟩ ≠ 0 → g / y ⟨(), t⟩ ^ d ∈ chartRingZ y (fun _ => t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«mem_chartLat_iff» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
