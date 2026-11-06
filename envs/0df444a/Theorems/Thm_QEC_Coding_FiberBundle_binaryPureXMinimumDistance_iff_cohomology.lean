-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_binaryPureXMinimumDistance_iff_cohomology
-- name    : QEC.Coding.FiberBundle.binaryPureXMinimumDistance_iff_cohomology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:10.991053+00:00
-- url     : https://prove2.me/theorems/6a2a25bc-e2b9-4d1d-a233-843aaa76f9dc
-- title:
--   Fiber Bundle: binary Pure XMinimum Distance iff cohomology
-- statement:
--   Exact pure-X distance is precisely an attained nontrivial cohomology weight
--   together with the corresponding universal lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Distance.lean#L51-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Distance.lean#L51-L88

import Definitions.Def_QEC_Coding_FiberBundle_Core
import Definitions.Def_QEC_Coding_FiberBundle_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.binaryPureXMinimumDistance_iff_cohomology
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) :
    BinaryPureXMinimumDistance D d ↔
      (∃ x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
        x ∈ (chainComplex D).middleCocycleCode.carrier ∧
        x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier ∧
        HammingWeight x = d) ∧
      CohomologyDistanceAtLeast D d := by sorry
