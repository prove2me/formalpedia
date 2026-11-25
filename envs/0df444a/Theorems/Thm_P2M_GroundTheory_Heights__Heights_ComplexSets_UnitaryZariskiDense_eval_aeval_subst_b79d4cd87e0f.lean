-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_eval_aeval_subst_b79d4cd87e0f
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_eval_aeval_subst_b79d4cd87e0f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:06.122998+00:00
-- url     : https://prove2.me/theorems/580b7cf9-44e4-50b5-a81c-65d0759d1fc9
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense eval aeval subst b79d4cd87e0f: P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense eval aeval subst b79d4cd87e
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense eval aeval subst b79d4cd87e0f construction uses the P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense eval aeval subst b79d4cd87e0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PUnitaryZariskiDense.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PUnitaryZariskiDense.lean#L13-L18

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_eval_aeval_subst_b79d4cd87e0f {σ τ : Type*} (F : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ)
    (x : τ → ℂ) : eval x (aeval F p) = eval (fun i => eval x (F i)) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«UnitaryZariskiDense».«eval_aeval_subst» := P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_eval_aeval_subst_b79d4cd87e0f
