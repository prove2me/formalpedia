-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_twistGraphWordOfHorizontalComponent
-- name    : QEC.Coding.FiberBundle.hammingWeight_twistGraphWordOfHorizontalComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:38.653006+00:00
-- url     : https://prove2.me/theorems/4f3c50ed-c94a-4fd1-a3f8-6e1279e046c2
-- title:
--   Fiber Bundle: hamming Weight twist Graph Word Of Horizontal Component
-- statement:
--   The twist-graph word of a residue-normalized representative has exactly the
--   full horizontal-sector Hamming weight; no coordinates are discarded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2151-L2165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2151-L2165

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_twistGraphWordOfHorizontalComponent
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z) :
    HammingWeight (twistGraphWordOfHorizontalComponent z) =
      HammingWeight (horizontalComponent z) := by sorry
