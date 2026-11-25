-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_eq_alternant_004e7763e2b2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_eq_alternant_004e7763e2b2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:38.369903+00:00
-- url     : https://prove2.me/theorems/8bfd3e74-94aa-4840-ade4-ed100f64ea28
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of X eq alternant 004e7763e2b2: P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of X eq alternant 004e7763e2b2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of X eq alternant 004e7763e2b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L23-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSmallBlockProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_eq_alternant_004e7763e2b2 (m : ℕ) :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun j : Fin m => m - 1 - (j : ℕ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchSmallBlockProduct».«vandermondeOf_X_eq_alternant» := P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_eq_alternant_004e7763e2b2
