-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_exists_place_of_valuationSubring_ca02ac74434f
-- name    : P2M_GroundTheory_Heights__Heights_CentredRingNormal_exists_place_of_valuationSubring_ca02ac74434f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:22.340944+00:00
-- url     : https://prove2.me/theorems/20ad59f0-41db-4617-8abc-2b585da62fc5
-- title:
--   P2 M Ground Theory Heights  Heights Centred Ring Normal exists place of valuation Subring ca02ac74434f: P2 M Ground Theory Heights  Heights Centred Ring Normal exists place of valuation Subring ca02ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Centred Ring Normal exists place of valuation Subring ca02ac74434f construction uses the P2 M Ground Theory Heights  Heights Centred Ring Normal exists place of valuation Subring ca02ac74434f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L30-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L30-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal
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
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]

theorem P2M_GroundTheory_Heights__Heights_CentredRingNormal_exists_place_of_valuationSubring_ca02ac74434f (V : ValuationSubring L) (hV : V ≠ ⊤) :
    ∃ w : FinitePlace L, ∀ x : L, x ∈ V ↔ w x ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CentredRingNormal».«exists_place_of_valuationSubring» := P2M_GroundTheory_Heights__Heights_CentredRingNormal_exists_place_of_valuationSubring_ca02ac74434f
