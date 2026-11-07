-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_leftProductKernel_eq_card_kernel_pow
-- name    : QEC.Coding.ProductExpansion.card_leftProductKernel_eq_card_kernel_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:37.2992+00:00
-- url     : https://prove2.me/theorems/b49a6095-9553-451a-af24-d3f6a18cb465
-- title:
--   Product Expansion: card left Product Kernel eq card kernel pow
-- statement:
--   Exact number of parity-check matrices annihilated by a fixed left
--   syndrome matrix. This is the finite counting form of the PK22 random-matrix
--   probability calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L428-L434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L428-L434

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq F] [Fintype R']

theorem QEC.Coding.ProductExpansion.card_leftProductKernel_eq_card_kernel_pow
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} =
      (Nat.card (LinearMap.ker M.mulVecLin)) ^ Nat.card R := by sorry
