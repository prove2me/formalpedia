-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_linForm_eq_linEval_0b701086e2ba
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_linForm_eq_linEval_0b701086e2ba
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:21.70016+00:00
-- url     : https://prove2.me/theorems/fe2465e8-a271-53f5-bc43-dff9cdcc8692
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval lin Form eq lin Eval 0b701086e2ba: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval lin Form eq lin Eval 0b701086e2ba construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eval lin Form eq lin Eval 0b701086e2ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchesToGoodPosition.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchesToGoodPosition.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsLocalBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsBranchesGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsPowerUnitCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchesToGoodPosition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_linForm_eq_linEval_0b701086e2ba {n : ℕ} (u x : Fin n → ℂ) :
    eval x (linForm u) = GroundTheory.Heights₂.Heights.linEval u x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eval_linForm_eq_linEval» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_linForm_eq_linEval_0b701086e2ba
