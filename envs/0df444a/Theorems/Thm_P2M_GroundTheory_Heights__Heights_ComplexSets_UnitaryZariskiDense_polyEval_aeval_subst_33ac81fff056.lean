-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_polyEval_aeval_subst_33ac81fff056
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_polyEval_aeval_subst_33ac81fff056
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:05.115201+00:00
-- url     : https://prove2.me/theorems/30bd4935-26cd-57eb-aed1-e4d6e3cde849
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense poly Eval aeval subst 33ac81fff056: P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense poly Eval aeval subst
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense poly Eval aeval subst 33ac81fff056 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense poly Eval aeval subst 33ac81fff056 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PUnitaryZariskiDense.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PUnitaryZariskiDense.lean#L20-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix Complex
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_polyEval_aeval_subst_33ac81fff056 {σ : Type*} (F : σ → Polynomial ℂ) (p : MvPolynomial σ ℂ) (z : ℂ) :
    (aeval F p).eval z = eval (fun i => (F i).eval z) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«UnitaryZariskiDense».«polyEval_aeval_subst» := P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_polyEval_aeval_subst_33ac81fff056
