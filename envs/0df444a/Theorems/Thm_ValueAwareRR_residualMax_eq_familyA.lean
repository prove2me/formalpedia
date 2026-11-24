-- Prove2me | Theorems.Thm_ValueAwareRR_residualMax_eq_familyA
-- name    : ValueAwareRR.residualMax_eq_familyA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:03:00.80065+00:00
-- url     : https://prove2.me/theorems/fa35705b-d972-4fa1-b413-a3dab60a3527
-- title:
--   Value Aware RR: residual Max eq family A
-- statement:
--   The Value Aware RR construction uses the residual Max eq family A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L617-L623
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L617-L623

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.residualMax_eq_familyA (m : ℚ) (hm : 2 ≤ m) :
    residualMax m = familyA m := by sorry
