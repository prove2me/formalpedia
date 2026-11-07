-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_powerset_pow_card_mul_pow_card_sub
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_powerset_pow_card_mul_pow_card_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:03.424751+00:00
-- url     : https://prove2.me/theorems/d2bc9629-14a5-4cc9-a250-cebec1b0afc7
-- title:
--   Random Base: sum powerset pow card mul pow card sub
-- statement:
--   Exact two-weight binomial enumeration of subsets.  It is used to sum
--   neighborhood occupancy masses after applying an exponential test weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L496-L509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L496-L509

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.sum_powerset_pow_card_mul_pow_card_sub
    {α : Type*} [DecidableEq α]
    (carrier : Finset α) (hit avoid : ENNReal) :
    ∑ T ∈ carrier.powerset,
        hit ^ T.card * avoid ^ (carrier.card - T.card) =
      (hit + avoid) ^ carrier.card := by sorry
