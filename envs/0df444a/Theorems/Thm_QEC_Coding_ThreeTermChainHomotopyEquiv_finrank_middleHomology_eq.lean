-- Prove2me | Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_finrank_middleHomology_eq
-- name    : QEC.Coding.ThreeTermChainHomotopyEquiv.finrank_middleHomology_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:59:10.942204+00:00
-- url     : https://prove2.me/theorems/e71790bd-dee4-46c6-bc63-f7791f3fd49d
-- title:
--   Three Term Chain Homotopy Equiv: finrank middle Homology eq
-- statement:
--   Chain-homotopy equivalent finite-coordinate complexes have equal logical
--   dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Homotopy.lean#L307-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Homotopy.lean#L307-L311

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq

set_option autoImplicit false
open QEC QEC.Coding
universe u v w z
variable {F : Type u} [Field F]
variable {A0 A1 A2 : Type v}
variable {B0 B1 B2 : Type w}
variable {C0 C1 C2 : Type z}
variable [AddCommGroup A0] [Module F A0]
variable [AddCommGroup A1] [Module F A1]
variable [AddCommGroup A2] [Module F A2]
variable [AddCommGroup B0] [Module F B0]
variable [AddCommGroup B1] [Module F B1]
variable [AddCommGroup B2] [Module F B2]
variable [AddCommGroup C0] [Module F C0]
variable [AddCommGroup C1] [Module F C1]
variable [AddCommGroup C2] [Module F C2]
open QEC.Coding.ThreeTermChainHomotopyEquiv
variable [Fintype F]
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {A0 A2 : Type (max u v)} [AddCommGroup A0] [Module F A0]
  [AddCommGroup A2] [Module F A2]
variable {B0 B2 : Type (max u w)} [AddCommGroup B0] [Module F B0]
  [AddCommGroup B2] [Module F B2]
variable {A : ChainComplexData F A0 (Word F ι) A2}
variable {B : ChainComplexData F B0 (Word F κ) B2}

theorem QEC.Coding.ThreeTermChainHomotopyEquiv.finrank_middleHomology_eq
    (e : ThreeTermChainHomotopyEquiv A B) :
    Module.finrank F A.middleHomology =
      Module.finrank F B.middleHomology := by sorry
