-- Prove2me | Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_forward_map1_not_mem_middleBoundaryCode
-- name    : QEC.Coding.ThreeTermChainHomotopyEquiv.forward_map1_not_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:58:39.525055+00:00
-- url     : https://prove2.me/theorems/5589d506-ee51-48a9-8a4d-8c2ede09c235
-- title:
--   Three Term Chain Homotopy Equiv: forward map1 not mem middle Boundary Code
-- statement:
--   The forward middle map of a chain-homotopy equivalence cannot send a
--   nontrivial source homology representative to a target boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L51-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L51-L75

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
set_option autoImplicit false
open QEC QEC.Coding
universe u v w
open QEC.Coding.ThreeTermChainHomotopyEquiv
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
omit [DecidableEq F] [Fintype ι0] [Fintype ι2] [Fintype κ0] [Fintype κ2]

theorem QEC.Coding.ThreeTermChainHomotopyEquiv.forward_map1_not_mem_middleBoundaryCode
    (e : ThreeTermChainHomotopyEquiv A B)
    {z : Word F ι1}
    (hzCycle : z ∈ A.middleCycleCode.carrier)
    (hzNontrivial : z ∉ A.middleBoundaryCode.carrier) :
    e.forward.map1 z ∉ B.middleBoundaryCode.carrier := by sorry
