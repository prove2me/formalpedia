-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_eval_pointOf_42c0fcab6353
-- name    : P2M_GroundTheory_Heights__Heights_contDiff_eval_pointOf_42c0fcab6353
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:50.49624+00:00
-- url     : https://prove2.me/theorems/f2507575-3ea4-5b5d-a7c2-f0516cd126b9
-- title:
--   P2 M Ground Theory Heights  Heights cont Diff eval point Of 42c0fcab6353: P2 M Ground Theory Heights  Heights cont Diff eval point Of 42c0fcab6353
-- statement:
--   The P2 M Ground Theory Heights  Heights cont Diff eval point Of 42c0fcab6353 construction uses the P2 M Ground Theory Heights  Heights cont Diff eval point Of 42c0fcab6353 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L79-L84

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

theorem P2M_GroundTheory_Heights__Heights_contDiff_eval_pointOf_42c0fcab6353 (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ 1 (fun w => eval (h.pointOf w) q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«contDiff_eval_pointOf» := P2M_GroundTheory_Heights__Heights_contDiff_eval_pointOf_42c0fcab6353
