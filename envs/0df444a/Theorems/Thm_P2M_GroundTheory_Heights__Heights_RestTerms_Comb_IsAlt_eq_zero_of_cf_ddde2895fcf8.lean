-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_zero_of_cf_ddde2895fcf8
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_zero_of_cf_ddde2895fcf8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:26.632582+00:00
-- url     : https://prove2.me/theorems/bf0358db-d327-53b7-a403-8f1f1cf353e7
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq zero of cf ddde2895fcf8: P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq zero of cf ddde2895fcf8
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq zero of cf ddde2895fcf8 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Is Alt eq zero of cf ddde2895fcf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L218-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L218-L232

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_zero_of_cf_ddde2895fcf8 {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P)
    (h : ∀ l : Fin m → ℕ, StrictAnti l → cf l P = 0) : P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«IsAlt».«eq_zero_of_cf» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_zero_of_cf_ddde2895fcf8
