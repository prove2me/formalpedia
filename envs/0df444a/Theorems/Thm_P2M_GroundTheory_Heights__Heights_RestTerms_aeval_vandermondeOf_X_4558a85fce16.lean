-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_aeval_vandermondeOf_X_4558a85fce16
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_aeval_vandermondeOf_X_4558a85fce16
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:13.410585+00:00
-- url     : https://prove2.me/theorems/45e3324f-68a7-5d83-a841-6006784b7ce2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms aeval vandermonde Of X 4558a85fce16: P2 M Ground Theory Heights  Heights Rest Terms aeval vandermonde Of X 4558a85fce16
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms aeval vandermonde Of X 4558a85fce16 construction uses the P2 M Ground Theory Heights  Heights Rest Terms aeval vandermonde Of X 4558a85fce16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchRootOfUnityBialternant.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchRootOfUnityBialternant.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityBialternant
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_aeval_vandermondeOf_X_4558a85fce16 {m : ℕ} (v : Fin m → ℂ) :
    aeval v (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) = vandermondeOf v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«aeval_vandermondeOf_X» := P2M_GroundTheory_Heights__Heights_RestTerms_aeval_vandermondeOf_X_4558a85fce16
