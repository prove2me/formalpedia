-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_IsHorizontalWeightMinimal_normalized
-- name    : QEC.Coding.FiberBundle.IsHorizontalWeightMinimal.normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:53:11.774197+00:00
-- url     : https://prove2.me/theorems/cac1ff56-a926-4d2e-8498-c67131f9c9bc
-- title:
--   Is Horizontal Weight Minimal: normalized
-- statement:
--   Fiberwise normalization preserves horizontal minimality after applying the
--   explicit induced base shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2303-L2362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2303-L2362

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.IsHorizontalWeightMinimal.normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hMinimal : IsHorizontalWeightMinimal baseSample twistSample x u) :
    IsHorizontalWeightMinimal baseSample twistSample
      (x + normalizationBaseShift baseSample u)
      (QEC.Coding.FiberBundle.normalizeC0Fibers u) := by sorry
