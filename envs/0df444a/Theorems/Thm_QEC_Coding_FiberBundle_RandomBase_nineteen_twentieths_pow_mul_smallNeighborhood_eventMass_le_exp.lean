-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp
-- name    : QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:07.232305+00:00
-- url     : https://prove2.me/theorems/6fd0964c-2e13-457e-84c6-abd28cd13643
-- title:
--   Random Base: nineteen twentieths pow mul small Neighborhood event Mass le exp
-- statement:
--   Exponential form of the concrete fixed-set lower-tail bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L917-L972
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L917-L972

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    ((19 : ENNReal) / 20) ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      ENNReal.ofReal
        (Real.exp
          (-((399997 : Real) * Delta * S.card / 8000000))) := by sorry
