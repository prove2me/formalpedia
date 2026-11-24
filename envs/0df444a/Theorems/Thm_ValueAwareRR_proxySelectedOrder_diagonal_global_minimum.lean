-- Prove2me | Theorems.Thm_ValueAwareRR_proxySelectedOrder_diagonal_global_minimum
-- name    : ValueAwareRR.proxySelectedOrder_diagonal_global_minimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T09:01:48.835634+00:00
-- url     : https://prove2.me/theorems/45b4c303-2e37-45bf-8a89-562f6b50ee27
-- title:
--   Value Aware RR: proxy Selected Order diagonal global minimum
-- statement:
--   The Value Aware RR construction uses the proxy Selected Order diagonal global minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L506-L523
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L506-L523

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.proxySelectedOrder_diagonal_global_minimum
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    diagonalScore m proxySelectedOrder ≤ diagonalScore m o := by sorry
