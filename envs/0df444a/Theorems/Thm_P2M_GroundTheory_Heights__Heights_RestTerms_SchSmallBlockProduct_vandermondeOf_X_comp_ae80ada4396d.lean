-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_comp_ae80ada4396d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_comp_ae80ada4396d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:40.905827+00:00
-- url     : https://prove2.me/theorems/648c2b9b-84c7-4984-b7bb-39709e6ffbc5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of X comp ae80ada4396d: P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of X comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of X comp ae80ada4396d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Small Block Product vandermonde Of X comp ae80ada4396d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchSmallBlockProduct.lean#L18-L21

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_comp_ae80ada4396d {m : ℕ} {κ : Type*} (g : Fin m → κ) :
    vandermondeOf (fun i => (X (g i) : MvPolynomial κ ℚ)) =
      rename g (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchSmallBlockProduct».«vandermondeOf_X_comp» := P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_comp_ae80ada4396d
