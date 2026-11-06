-- Prove2me | Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_inverse_transpose_map1_not_mem_firstCoboundaryCheckCode
-- name    : QEC.Coding.ThreeTermChainHomotopyEquiv.inverse_transpose_map1_not_mem_firstCoboundaryCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:58:35.746304+00:00
-- url     : https://prove2.me/theorems/c8035d81-809c-466b-ae2a-742ab7bdf5c2
-- title:
--   Three Term Chain Homotopy Equiv: inverse transpose map1 not mem first Coboundary Check Code
-- statement:
--   The transpose of the inverse middle map cannot send a nontrivial source
--   cohomology representative to a target coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L100-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/HomotopyDistance.lean#L100-L125

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
omit [DecidableEq F]

theorem QEC.Coding.ThreeTermChainHomotopyEquiv.inverse_transpose_map1_not_mem_firstCoboundaryCheckCode
    (e : ThreeTermChainHomotopyEquiv A B)
    {x : Word F ι1}
    (hxCocycle : x ∈ A.middleCocycleCode.carrier)
    (hxNontrivial : x ∉ A.firstCoboundaryCheckCode.carrier) :
    wordLinearMapTranspose e.inverse.map1 x ∉
      B.firstCoboundaryCheckCode.carrier := by sorry
