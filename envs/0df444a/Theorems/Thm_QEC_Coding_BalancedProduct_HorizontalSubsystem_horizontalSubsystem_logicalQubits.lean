-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_horizontalSubsystem_logicalQubits
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalSubsystem_logicalQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:37:46.315546+00:00
-- url     : https://prove2.me/theorems/7e153ba1-b78f-4b3a-9809-da51e30e6655
-- title:
--   Horizontal Subsystem: horizontal Subsystem logical Qubits
-- statement:
--   The Horizontal Subsystem construction uses the horizontal Subsystem logical Qubits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L632-L640
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L632-L640

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalSubsystem_logicalQubits
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (hOdd : Odd (Fintype.card G)) :
    (horizontalSubsystem A x hOdd).logicalQubits =
      Module.finrank (ZMod 2) (quotientTannerComplex A).middleHomology := by sorry
