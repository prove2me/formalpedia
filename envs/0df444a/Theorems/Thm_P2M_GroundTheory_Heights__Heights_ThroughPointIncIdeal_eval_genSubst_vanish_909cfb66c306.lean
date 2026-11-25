-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_genSubst_vanish_909cfb66c306
-- name    : P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_genSubst_vanish_909cfb66c306
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:07.654074+00:00
-- url     : https://prove2.me/theorems/14da079f-d3b7-573e-a0a3-94c3a5a30cbd
-- title:
--   P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval gen Subst vanish 909cfb66c306: P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval gen Subst vanish 909cfb66c306
-- statement:
--   The P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval gen Subst vanish 909cfb66c306 construction uses the P2 M Ground Theory Heights  Heights Through Point Inc Ideal eval gen Subst vanish 909cfb66c306 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PThroughPointIncIdeal.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PThroughPointIncIdeal.lean#L19-L24

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

theorem P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_genSubst_vanish_909cfb66c306 {K : Type*} [Field K] {n k : ℕ} (x c : Fin n → K)
    (hc : ∑ j, c j * x j = 1) (a : Fin k × Fin n → K) (i : Fin k) :
    ∑ j, eval a (genSubst (k := k) x c (i, j)) * x j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ThroughPointIncIdeal».«eval_genSubst_vanish» := P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_genSubst_vanish_909cfb66c306
