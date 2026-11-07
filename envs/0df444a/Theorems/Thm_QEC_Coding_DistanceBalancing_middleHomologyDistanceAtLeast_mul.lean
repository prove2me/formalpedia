-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_middleHomologyDistanceAtLeast_mul
-- name    : QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:39.712971+00:00
-- url     : https://prove2.me/theorems/0162db36-6b56-4951-ae38-9003aa5f062a
-- title:
--   Distance Balancing: middle Homology Distance At Least mul
-- statement:
--   EKZ20 Theorem 2.3, multiplicative homological-distance bound.  The
--   homology-valued slice word satisfies the classical parity checks; a dual
--   functional detects one nonzero slice and turns it into an ordinary nonzero
--   classical codeword.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1371-L1386
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1371-L1386

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast_mul
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {dSource dClassical : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical) :
    MiddleHomologyDistanceAtLeast
      (chainComplex D) (dClassical * dSource) := by sorry
