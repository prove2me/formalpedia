-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_binaryCSSCode_finrank_carrier
-- name    : QEC.Coding.LiftedProduct.binaryCSSCode_finrank_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:10.91904+00:00
-- url     : https://prove2.me/theorems/f48d52de-1fa7-4a83-a221-9ef2d07b0ba9
-- title:
--   Lifted Product: binary CSSCode finrank carrier
-- statement:
--   The semantic carrier dimension of the induced binary CSS code is `2` to the
--   middle-homology dimension of its lifted-product chain complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1006-L1018
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1006-L1018

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.binaryCSSCode_finrank_carrier
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    Module.finrank Complex (binaryCSSCode D).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) (chainComplex D).middleHomology := by sorry
