-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_avoidsOutside_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.avoidsOutside_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:57.935199+00:00
-- url     : https://prove2.me/theorems/ba2f1eed-d435-49f6-943f-e7796c86d832
-- title:
--   Random Base: avoids Outside event Mass
-- statement:
--   Exact probability of a fixed neighborhood-containment witness.  This is the
--   Bernoulli analogue of the paper's regular-model counting step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L492-L572
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L492-L572

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.avoidsOutside_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (AvoidsOutside S T) =
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        (S.card * (4 * r - T.card))) := by sorry
