-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_ell_mul_coarseFiberWord
-- name    : QEC.Coding.FiberBundle.hammingWeight_eq_ell_mul_coarseFiberWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:23.753552+00:00
-- url     : https://prove2.me/theorems/96e3076a-8c8c-4c38-92a4-a08bd185a342
-- title:
--   Fiber Bundle: hamming Weight eq ell mul coarse Fiber Word
-- statement:
--   A block-constant fine word has exactly `ell` copies of every coarse-layer
--   bit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2429-L2477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2429-L2477

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_eq_ell_mul_coarseFiberWord
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    HammingWeight v =
      ell * HammingWeight (coarseFiberWord ell v) := by sorry
