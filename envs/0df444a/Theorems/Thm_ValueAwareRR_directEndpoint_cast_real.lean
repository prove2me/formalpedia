-- Prove2me | Theorems.Thm_ValueAwareRR_directEndpoint_cast_real
-- name    : ValueAwareRR.directEndpoint_cast_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:07:33.393785+00:00
-- url     : https://prove2.me/theorems/4d933bd2-6c92-4b94-b24a-f4f123fc0eb7
-- title:
--   Value Aware RR: direct Endpoint cast real
-- statement:
--   The rational endpoint identity embeds unchanged into the manuscript's real model.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L262-L264
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L262-L264

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.directEndpoint_cast_real (m : ℚ) (o : SignedOrder) :
    ((directEndpoint m o : ℚ) : ℝ) = ((filteredSum m o : ℚ) : ℝ) / 9 := by sorry
