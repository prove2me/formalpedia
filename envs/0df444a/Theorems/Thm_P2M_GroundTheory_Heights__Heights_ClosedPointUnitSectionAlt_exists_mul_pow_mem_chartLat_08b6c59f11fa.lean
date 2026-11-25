-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_mul_pow_mem_chartLat_08b6c59f11fa
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_mul_pow_mem_chartLat_08b6c59f11fa
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:25.145454+00:00
-- url     : https://prove2.me/theorems/7f346da4-0220-4dd0-926b-a771b28c8ddf
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists mul pow mem chart Lat 08b6c59f11fa: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists mul pow mem chart
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists mul pow mem chart Lat 08b6c59f11fa construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt exists mul pow mem chart Lat 08b6c59f11fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L64-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L64-L96

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

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_mul_pow_mem_chartLat_08b6c59f11fa (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ chartRingZ y (fun _ => t)) : ∃ k : ℕ, x * y ⟨(), t⟩ ^ k ∈ chartLat y 1 k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«exists_mul_pow_mem_chartLat» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_mul_pow_mem_chartLat_08b6c59f11fa
