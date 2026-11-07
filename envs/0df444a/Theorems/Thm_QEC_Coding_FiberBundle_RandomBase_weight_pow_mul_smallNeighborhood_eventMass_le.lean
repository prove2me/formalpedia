-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_weight_pow_mul_smallNeighborhood_eventMass_le
-- name    : QEC.Coding.FiberBundle.RandomBase.weight_pow_mul_smallNeighborhood_eventMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:13.031415+00:00
-- url     : https://prove2.me/theorems/9aa7b181-1f42-4cae-92c3-542ba61cc5b5
-- title:
--   Random Base: weight pow mul small Neighborhood event Mass le
-- statement:
--   Subunit exponential test weights control the lower tail without division:
--   `z^k P(|N(S)| ≤ k)` is at most the exact probability-generating function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L811-L859
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L811-L859

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.weight_pow_mul_smallNeighborhood_eventMass_le
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) (cutoff : Nat)
    (weight : ENNReal) (hweight : weight ≤ 1) :
    weight ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      (weight *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) +
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ (4 * r) := by sorry
