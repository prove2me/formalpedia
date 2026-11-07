-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
-- name    : QEC.Coding.FiberBundle.ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:52.680529+00:00
-- url     : https://prove2.me/theorems/6357eebe-0cf2-42dc-ac4b-aa7015384e3a
-- title:
--   Fiber Bundle: ell mul hamming Weight cycle Boundary le two mul hamming Weight
-- statement:
--   Quantitative string counting: every nonzero coarse boundary endpoint costs a
--   length-`ell` block, with the factor two accounting for the two endpoints of
--   each binary run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2606-L2634
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2606-L2634

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    ell * HammingWeight (cycleFiberChainBoundary (ell * ell) v) ≤
      2 * HammingWeight v := by sorry
