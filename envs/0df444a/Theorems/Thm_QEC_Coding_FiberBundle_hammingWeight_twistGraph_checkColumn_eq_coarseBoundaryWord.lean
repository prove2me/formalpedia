-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
-- name    : QEC.Coding.FiberBundle.hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:50.958376+00:00
-- url     : https://prove2.me/theorems/2ee7ca39-3e73-409e-8e02-e1ae93205b81
-- title:
--   Fiber Bundle: hamming Weight twist Graph check Column eq coarse Boundary Word
-- statement:
--   For a fixed base check, twist violations across source layers are a
--   permutation of the sampled coarse boundary of the corresponding vertical
--   fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2822-L2861
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2822-L2861

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (a : Fin (3 * r)) :
    HammingWeight
        (TwistGraph.checkColumn baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) a) =
      HammingWeight (coarseBoundaryWord ell (verticalFiber z a)) := by sorry
