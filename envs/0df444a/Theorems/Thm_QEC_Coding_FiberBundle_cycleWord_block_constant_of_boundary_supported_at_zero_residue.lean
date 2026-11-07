-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cycleWord_block_constant_of_boundary_supported_at_zero_residue
-- name    : QEC.Coding.FiberBundle.cycleWord_block_constant_of_boundary_supported_at_zero_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:43.005788+00:00
-- url     : https://prove2.me/theorems/2b729b7f-4842-4b42-a113-485b57761bc0
-- title:
--   Fiber Bundle: cycle Word block constant of boundary supported at zero residue
-- statement:
--   If the fine cycle boundary is supported at residue-zero positions, the word
--   is constant throughout every length-`ell` block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2351-L2416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2351-L2416

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.cycleWord_block_constant_of_boundary_supported_at_zero_residue
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0)
    (u : ZMod ell) (k : Fin ell) :
    v (TwistGraph.blockPosition ell (u, k)) =
      v (TwistGraph.layerEmbedding ell u) := by sorry
