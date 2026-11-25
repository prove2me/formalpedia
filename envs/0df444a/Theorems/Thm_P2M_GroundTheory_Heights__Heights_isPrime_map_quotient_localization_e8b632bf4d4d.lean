-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_quotient_localization_e8b632bf4d4d
-- name    : P2M_GroundTheory_Heights__Heights_isPrime_map_quotient_localization_e8b632bf4d4d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:07.304072+00:00
-- url     : https://prove2.me/theorems/bf8c3b6b-ca18-41a3-a0f7-45d63150fba2
-- title:
--   P2 M Ground Theory Heights  Heights is Prime map quotient localization e8b632bf4d4d: P2 M Ground Theory Heights  Heights is Prime map quotient localization e8b632bf4d4d
-- statement:
--   The P2 M Ground Theory Heights  Heights is Prime map quotient localization e8b632bf4d4d construction uses the P2 M Ground Theory Heights  Heights is Prime map quotient localization e8b632bf4d4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalizeQuotientStages.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalizeQuotientStages.lean#L10-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
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
universe u
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isPrime_map_quotient_localization_e8b632bf4d4d {R : Type*} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    (hWm : W ≤ m) (hIW : I ≤ W) :
    (W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m)))).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isPrime_map_quotient_localization» := P2M_GroundTheory_Heights__Heights_isPrime_map_quotient_localization_e8b632bf4d4d
