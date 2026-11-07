-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_exists_normalized_horizontalWeightMinimal
-- name    : QEC.Coding.FiberBundle.exists_normalized_horizontalWeightMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:32:12.802621+00:00
-- url     : https://prove2.me/theorems/d2029c29-9567-4a00-a966-b12c942b3ee4
-- title:
--   Fiber Bundle: exists normalized horizontal Weight Minimal
-- statement:
--   Every nontrivial lifted base class admits a correction whose normalized,
--   base-shifted presentation is simultaneously nonzero in the base direction,
--   fiberwise normalized, and horizontal-weight minimal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2426-L2446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L2426-L2446

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.exists_normalized_horizontalWeightMinimal
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
      IsHorizontalWeightMinimal baseSample twistSample
        (x + normalizationBaseShift baseSample u)
        (normalizeC0Fibers u) := by sorry
