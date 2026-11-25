-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:44.005214+00:00
-- url     : https://prove2.me/theorems/310677af-6b84-4f0e-91f7-871261b3cfde
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of X eq alt 52fd29888339: P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of X eq alt 52fd29888339
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of X eq alt 52fd29888339 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of X eq alt 52fd29888339 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L150-L152

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339 :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) = alt (stair m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«vandermondeOf_X_eq_alt» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339
