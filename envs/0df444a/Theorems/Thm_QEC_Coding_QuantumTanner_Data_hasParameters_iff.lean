-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_hasParameters_iff
-- name    : QEC.Coding.QuantumTanner.Data.hasParameters_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:55:29.766043+00:00
-- url     : https://prove2.me/theorems/b7589864-de39-4265-a37b-5aede0df04df
-- title:
--   Data: has Parameters iff
-- statement:
--   The Data construction uses the has Parameters iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L394-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L394-L401

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.hasParameters_iff (D : Data G A B Square XBasis ZBasis) (n k d : Nat) :
    D.HasParameters n k d ↔
      n = Fintype.card Square ∧
      k = Module.finrank (ZMod 2) D.chainComplex.middleHomology ∧
      AlgebraicCSSMinimumDistance
        D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode d := by sorry
