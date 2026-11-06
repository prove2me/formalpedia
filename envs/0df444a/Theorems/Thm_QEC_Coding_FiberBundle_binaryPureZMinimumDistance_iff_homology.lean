-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_binaryPureZMinimumDistance_iff_homology
-- name    : QEC.Coding.FiberBundle.binaryPureZMinimumDistance_iff_homology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:59.573282+00:00
-- url     : https://prove2.me/theorems/f7435fd1-27f2-4a59-bd0a-7a55cf076564
-- title:
--   Fiber Bundle: binary Pure ZMinimum Distance iff homology
-- statement:
--   Exact pure-Z distance is precisely an attained nontrivial homology weight
--   together with the corresponding universal lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Distance.lean#L94-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Distance.lean#L94-L131

import Definitions.Def_QEC_Coding_FiberBundle_Core
import Definitions.Def_QEC_Coding_FiberBundle_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.binaryPureZMinimumDistance_iff_homology
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) :
    BinaryPureZMinimumDistance D d ↔
      (∃ z : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
        z ∈ (chainComplex D).middleCycleCode.carrier ∧
        z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
        HammingWeight z = d) ∧
      HomologyDistanceAtLeast D d := by sorry
