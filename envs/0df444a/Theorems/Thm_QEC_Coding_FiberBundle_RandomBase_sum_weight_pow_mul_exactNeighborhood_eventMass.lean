-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_weight_pow_mul_exactNeighborhood_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.sum_weight_pow_mul_exactNeighborhood_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:50:44.873505+00:00
-- url     : https://prove2.me/theorems/81b7030c-7f6c-4ed6-bc59-256b18f8833c
-- title:
--   Random Base: sum weight pow mul exact Neighborhood event Mass
-- statement:
--   Exact probability-generating function of the neighborhood size of a fixed
--   check set.  It is derived from the construction-owned sample distribution and
--   the exact-neighborhood partition, not postulated as a binomial law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L693-L737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L693-L737

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.sum_weight_pow_mul_exactNeighborhood_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) (weight : ENNReal) :
    (∑ T : Finset (Fin (4 * r)),
        weight ^ T.card *
          eventMass
            (distribution r Delta hDelta)
            (fun sample => checkSetNeighborhood sample S = T)) =
      (weight *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) +
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ (4 * r) := by sorry
