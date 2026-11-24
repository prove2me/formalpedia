-- Prove2me | Theorems.Thm_ValueAwareRR_orderedResidual_signReverse
-- name    : ValueAwareRR.orderedResidual_signReverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:53:14.287802+00:00
-- url     : https://prove2.me/theorems/1aa01b1f-b8b6-494c-874e-b3da78d91656
-- title:
--   Value Aware RR: ordered Residual sign Reverse
-- statement:
--   The Value Aware RR construction uses the ordered Residual sign Reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L188-L193
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L188-L193

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.orderedResidual_signReverse (m : ℚ) (o : SignedOrder) (k : Fin 4) :
    orderedResidual m (signReverse o) k = -orderedResidual m o k := by sorry
