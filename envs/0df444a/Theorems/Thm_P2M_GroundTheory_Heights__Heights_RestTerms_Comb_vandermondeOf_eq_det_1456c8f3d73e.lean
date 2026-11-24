-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_eq_det_1456c8f3d73e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_eq_det_1456c8f3d73e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:18.060814+00:00
-- url     : https://prove2.me/theorems/162b9a96-641b-41c3-9eba-1790c763cc20
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of eq det 1456c8f3d73e: P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of eq det 1456c8f3d73e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of eq det 1456c8f3d73e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb vandermonde Of eq det 1456c8f3d73e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L146-L148

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_eq_det_1456c8f3d73e {R : Type*} [CommRing R] (v : Fin m → R) :
    vandermondeOf v = (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«vandermondeOf_eq_det» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_eq_det_1456c8f3d73e
