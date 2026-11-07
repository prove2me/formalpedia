-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord
-- name    : QEC.Coding.FiberBundle.coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:37.124197+00:00
-- url     : https://prove2.me/theorems/3faeb5df-47a5-40fd-bd51-eb16ac069c87
-- title:
--   Fiber Bundle: coarse Boundary Word eq cycle Fiber Chain Boundary coarse Fiber Word
-- statement:
--   The sampled fine boundary is the cyclic boundary of the coarse word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2573-L2599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2573-L2599

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    coarseBoundaryWord ell v =
      cycleFiberChainBoundary ell (coarseFiberWord ell v) := by sorry
