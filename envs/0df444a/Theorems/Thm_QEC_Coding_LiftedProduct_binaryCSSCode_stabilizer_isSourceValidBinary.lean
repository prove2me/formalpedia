-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_binaryCSSCode_stabilizer_isSourceValidBinary
-- name    : QEC.Coding.LiftedProduct.binaryCSSCode_stabilizer_isSourceValidBinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:30:30.022238+00:00
-- url     : https://prove2.me/theorems/1af67761-105e-4398-a7ca-924f218b2871
-- title:
--   Lifted Product: binary CSSCode stabilizer is Source Valid Binary
-- statement:
--   The exact stabilizer of the induced binary CSS code satisfies source validity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L979-L988
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L979-L988

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.binaryCSSCode_stabilizer_isSourceValidBinary
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by sorry
