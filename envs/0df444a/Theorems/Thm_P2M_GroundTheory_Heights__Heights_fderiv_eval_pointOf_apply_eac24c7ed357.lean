-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fderiv_eval_pointOf_apply_eac24c7ed357
-- name    : P2M_GroundTheory_Heights__Heights_fderiv_eval_pointOf_apply_eac24c7ed357
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:26.940592+00:00
-- url     : https://prove2.me/theorems/2b9c6896-3e87-4251-849a-5c8574cb8e7c
-- title:
--   P2 M Ground Theory Heights  Heights fderiv eval point Of apply eac24c7ed357: P2 M Ground Theory Heights  Heights fderiv eval point Of apply eac24c7ed357
-- statement:
--   The P2 M Ground Theory Heights  Heights fderiv eval point Of apply eac24c7ed357 construction uses the P2 M Ground Theory Heights  Heights fderiv eval point Of apply eac24c7ed357 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L72-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_fderiv_eval_pointOf_apply_eac24c7ed357 (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℂ (fun w => eval (h.pointOf w) q) z v =
      ∑ j, eval (h.pointOf z) (pderiv j q) * h.pointOf v j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fderiv_eval_pointOf_apply» := P2M_GroundTheory_Heights__Heights_fderiv_eval_pointOf_apply_eac24c7ed357
