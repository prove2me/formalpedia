-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_normalized_weightMinimal
-- name    : QEC.Coding.FiberBundle.exists_normalized_weightMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:32:22.326121+00:00
-- url     : https://prove2.me/theorems/73fc32a2-bb64-444d-8066-6954bc93f3e0
-- title:
--   Fiber Bundle: exists normalized weight Minimal
-- statement:
--   Every nontrivial lifted base class admits a fiberwise-normalized presentation
--   which is nonzero in the base direction and minimizes full Hamming weight over
--   all degree-zero corrections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2453-L2473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2453-L2473

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_normalized_weightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x) :
    ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
      x + normalizationBaseShift baseSample u ≠ 0 ∧
      C0FibersNormalized (normalizeC0Fibers u) ∧
      IsWeightMinimal baseSample twistSample
        (x + normalizationBaseShift baseSample u)
        (normalizeC0Fibers u) := by sorry
