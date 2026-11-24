-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_of_strictAnti_30339c9c8742
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_of_strictAnti_30339c9c8742
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:42.774212+00:00
-- url     : https://prove2.me/theorems/205b6d91-098f-46ab-8131-fc010b95a68f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt of strict Anti 30339c9c8742: P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt of strict Anti 30339c9c8742
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt of strict Anti 30339c9c8742 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb cf alt of strict Anti 30339c9c8742 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L131-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_of_strictAnti_30339c9c8742 {l v : Fin m → ℕ} (hl : StrictAnti l) (hv : StrictAnti v) :
    cf l (alt v) = if l = v then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«cf_alt_of_strictAnti» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_of_strictAnti_30339c9c8742
