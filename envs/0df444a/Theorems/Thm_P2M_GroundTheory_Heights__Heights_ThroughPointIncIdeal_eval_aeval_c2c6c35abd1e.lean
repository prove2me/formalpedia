-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_aeval_c2c6c35abd1e
-- name    : P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_aeval_c2c6c35abd1e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:22.305087+00:00
-- url     : https://prove2.me/theorems/2185fe29-b198-4489-af68-83fec6e250f5
-- title:
--   P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval aeval c2c6c35abd1e: P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval aeval c2c6c35abd1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval aeval c2c6c35abd1e construction uses the P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval aeval c2c6c35abd1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PThroughPointIncIdeal.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PThroughPointIncIdeal.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PThroughPointIncIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_aeval_c2c6c35abd1e {F K : Type*} [Field F] [Field K] [Algebra F K] {σ τ : Type*}
    (s : σ → MvPolynomial τ K) (a : τ → K) (g : MvPolynomial σ F) :
    eval a (aeval s g) = aeval (fun i => eval a (s i)) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ThroughPointIncIdeal».«eval_aeval» := P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_aeval_c2c6c35abd1e
