-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
-- name    : QEC.Coding.FiberBundle.bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:58.600098+00:00
-- url     : https://prove2.me/theorems/3325a166-e43e-4d46-8883-c766a3d35ac4
-- title:
--   Fiber Bundle: bundle Coboundary constant Fiber Word eq horizontal Base Lift
-- statement:
--   The bundle coboundary of a constant-fiber word is exactly the lift of the
--   ordinary base coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L562-L608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L562-L608

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (constantFiberWord
          (fiberZero := ZMod (ell * ell)) t) =
      horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell))
        (baseCoboundary baseSample t) := by sorry
