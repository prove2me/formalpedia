-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingSupport_cycleBoundary_eq_image_coarseBoundaryWord
-- name    : QEC.Coding.FiberBundle.hammingSupport_cycleBoundary_eq_image_coarseBoundaryWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:30.384451+00:00
-- url     : https://prove2.me/theorems/ccc8e43b-8927-4510-944e-aea29db31690
-- title:
--   Fiber Bundle: hamming Support cycle Boundary eq image coarse Boundary Word
-- statement:
--   A residue-zero-supported fine boundary has exactly its coarse support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2521-L2555
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2521-L2555

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingSupport_cycleBoundary_eq_image_coarseBoundaryWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    hammingSupport (cycleFiberChainBoundary (ell * ell) v) =
      (hammingSupport (coarseBoundaryWord ell v)).image
        (TwistGraph.layerEmbedding ell) := by sorry
