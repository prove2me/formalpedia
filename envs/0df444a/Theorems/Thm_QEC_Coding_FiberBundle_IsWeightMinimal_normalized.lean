-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_IsWeightMinimal_normalized
-- name    : QEC.Coding.FiberBundle.IsWeightMinimal.normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:53:05.745193+00:00
-- url     : https://prove2.me/theorems/75188ce8-9610-42c9-909f-79193ba0bf40
-- title:
--   Is Weight Minimal: normalized
-- statement:
--   Full-weight minimality is preserved by normalization and its base shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2365-L2419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2365-L2419

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.IsWeightMinimal.normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hMinimal : IsWeightMinimal baseSample twistSample x u) :
    IsWeightMinimal baseSample twistSample
      (x + normalizationBaseShift baseSample u)
      (normalizeC0Fibers u) := by sorry
