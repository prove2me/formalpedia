-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_exists_detectingClassicalWord_of_product_nonboundary
-- name    : QEC.Coding.DistanceBalancing.exists_detectingClassicalWord_of_product_nonboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:21:30.526633+00:00
-- url     : https://prove2.me/theorems/30839eaf-b6bd-4fc4-823f-03f61cdfac78
-- title:
--   Distance Balancing: exists detecting Classical Word of product nonboundary
-- statement:
--   The Distance Balancing construction uses the exists detecting Classical Word of product nonboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1319-L1345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1319-L1345

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

theorem QEC.Coding.DistanceBalancing.exists_detectingClassicalWord_of_product_nonboundary
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {dSource : Nat}
    (hSource : MiddleHomologyDistanceAtLeast
      (sourceChainComplex D) dSource)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hNonboundary : z ∉ (chainComplex D).middleBoundaryCode.carrier) :
    ∃ w : Word (ZMod 2) classicalBit,
      Matrix.toLin' D.classicalBoundary w = 0 ∧
      w ≠ 0 ∧
      dSource * HammingWeight w ≤ HammingWeight z := by sorry
