-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_twistGraph_variableWord_eq_horizontalFiber
-- name    : QEC.Coding.FiberBundle.hammingWeight_twistGraph_variableWord_eq_horizontalFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:12.84212+00:00
-- url     : https://prove2.me/theorems/363dd8c5-16dc-45e0-a180-e400f110eb3f
-- title:
--   Fiber Bundle: hamming Weight twist Graph variable Word eq horizontal Fiber
-- statement:
--   Normalized horizontal fiber weight equals its twist-graph column weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2129-L2145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2129-L2145

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_twistGraph_variableWord_eq_horizontalFiber
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z)
    (b : Fin (4 * r)) :
    HammingWeight
        (TwistGraph.variableWord
          (twistGraphWordOfHorizontalComponent z) b) =
      HammingWeight (horizontalFiber z b) := by sorry
