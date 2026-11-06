-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_horizontalFiber_bundleCoboundary_eq_of_counique
-- name    : QEC.Coding.FiberBundle.exists_horizontalFiber_bundleCoboundary_eq_of_counique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:53:37.274174+00:00
-- url     : https://prove2.me/theorems/4fd94e68-6e92-46fb-bee5-111bc6b8aef4
-- title:
--   Fiber Bundle: exists horizontal Fiber bundle Coboundary eq of counique
-- statement:
--   Over a counique base variable, the horizontal coboundary fiber is a single
--   connection-reindexed fiber word.  All other selected checks are absent, while
--   fiber words outside `S` vanish by the stated support condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L798-L838
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L798-L838

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_horizontalFiber_bundleCoboundary_eq_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (S : Finset (Fin (3 * r))) (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample S)
    (hu : ∀ a, a ∉ S → c0Fiber u a = 0) :
    ∃ a ∈ S,
      baseSample (a, b) = true ∧
        horizontalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b =
          reindexWord
            ((RandomTwist.fiberBundleData baseSample twistSample).connection b a).onZero.symm
            (c0Fiber u a) := by sorry
