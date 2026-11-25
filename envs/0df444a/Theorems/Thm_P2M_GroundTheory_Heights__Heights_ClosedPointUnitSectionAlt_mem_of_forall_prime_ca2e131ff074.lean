-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_forall_prime_ca2e131ff074
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_forall_prime_ca2e131ff074
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:54.888082+00:00
-- url     : https://prove2.me/theorems/03daa8ae-4b65-4ce4-bb36-3f1ea17c7989
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of forall prime ca2e131ff074: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of forall prime ca2e131ff074
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of forall prime ca2e131ff074 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt mem of forall prime ca2e131ff074 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L317-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L317-L339

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
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_forall_prime_ca2e131ff074 (W : ValuationSubring K')
    (hW : ∀ q : ℕ, q.Prime → W.valuation (q : K') = 1) (x : K') : x ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«mem_of_forall_prime» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_of_forall_prime_ca2e131ff074
