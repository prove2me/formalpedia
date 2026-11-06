-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_binaryAlgebraicCSSMinimumDistance_of_sector_minima
-- name    : QEC.Coding.LiftedProduct.binaryAlgebraicCSSMinimumDistance_of_sector_minima
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:20.136775+00:00
-- url     : https://prove2.me/theorems/9989e055-6678-4ef8-bd86-51167ad3f964
-- title:
--   Lifted Product: binary Algebraic CSSMinimum Distance of sector minima
-- statement:
--   The two exact sector minima combine into the minimum for the induced code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1057-L1069
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1057-L1069

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.binaryAlgebraicCSSMinimumDistance_of_sector_minima
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol)
    {dX dZ : Nat}
    (hX : BinaryPureXMinimumDistance D dX)
    (hZ : BinaryPureZMinimumDistance D dZ) :
    BinaryAlgebraicCSSMinimumDistance D (min dX dZ) := by sorry
