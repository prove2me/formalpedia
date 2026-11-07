-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_cycleBoundary_eq_coarseBoundaryWord
-- name    : QEC.Coding.FiberBundle.hammingWeight_cycleBoundary_eq_coarseBoundaryWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:03.319491+00:00
-- url     : https://prove2.me/theorems/2447ec27-0390-4536-af70-22b3766fda28
-- title:
--   Fiber Bundle: hamming Weight cycle Boundary eq coarse Boundary Word
-- statement:
--   Fine boundary weight equals the sampled coarse-boundary weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2558-L2570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2558-L2570

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_cycleBoundary_eq_coarseBoundaryWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    HammingWeight (cycleFiberChainBoundary (ell * ell) v) =
      HammingWeight (coarseBoundaryWord ell v) := by sorry
