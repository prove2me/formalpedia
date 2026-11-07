-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
-- name    : QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:58.940096+00:00
-- url     : https://prove2.me/theorems/feee38c4-cef0-4a10-ab89-3ff2099d3870
-- title:
--   Random Base: nineteen twentieths pow mul small Neighborhood event Mass le
-- statement:
--   The concrete `19 / 20` lower-tail test for an HHO20-small check set, with a
--   fully explicit finite-power deficit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L865-L912
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L865-L912

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    ((19 : ENNReal) / 20) ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      (((1 -
          (1 : NNReal) / 20 *
            ((399997 : NNReal) / 400000 *
              ((S.card : NNReal) *
                incidenceProbability (4 * r) Delta)) : NNReal) :
        ENNReal) ^ (4 * r)) := by sorry
