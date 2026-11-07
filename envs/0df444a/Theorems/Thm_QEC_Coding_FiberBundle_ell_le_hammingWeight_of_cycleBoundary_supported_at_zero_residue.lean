-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_ell_le_hammingWeight_of_cycleBoundary_supported_at_zero_residue
-- name    : QEC.Coding.FiberBundle.ell_le_hammingWeight_of_cycleBoundary_supported_at_zero_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:53.013605+00:00
-- url     : https://prove2.me/theorems/8401676c-abd4-4026-8c52-b5c8e345646f
-- title:
--   Fiber Bundle: ell le hamming Weight of cycle Boundary supported at zero residue
-- statement:
--   A binary cycle chain whose nonzero boundary vertices all have residue zero
--   has weight at least `ell` whenever its boundary is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2640-L2779
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2640-L2779

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.ell_le_hammingWeight_of_cycleBoundary_supported_at_zero_residue
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0)
    (hBoundaryNonzero :
      cycleFiberChainBoundary (ell * ell) v ≠ 0) :
    ell ≤ HammingWeight v := by sorry
