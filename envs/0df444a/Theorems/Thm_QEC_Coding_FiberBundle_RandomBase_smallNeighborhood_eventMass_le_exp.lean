-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_smallNeighborhood_eventMass_le_exp
-- name    : QEC.Coding.FiberBundle.RandomBase.smallNeighborhood_eventMass_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:31.608985+00:00
-- url     : https://prove2.me/theorems/e084b9d1-987f-47f5-b7b2-c9d6bc330b29
-- title:
--   Random Base: small Neighborhood event Mass le exp
-- statement:
--   Unweighted fixed-set lower-tail bound after paying the reciprocal
--   `19 / 20` test-weight cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L978-L1044
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L978-L1044

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.smallNeighborhood_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      ENNReal.ofReal
        (Real.exp
          ((cutoff : Real) / 19 -
            (399997 : Real) * Delta * S.card / 8000000)) := by sorry
