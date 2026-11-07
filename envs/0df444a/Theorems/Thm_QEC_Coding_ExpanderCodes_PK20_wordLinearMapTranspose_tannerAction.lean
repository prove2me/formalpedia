-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_wordLinearMapTranspose_tannerAction
-- name    : QEC.Coding.ExpanderCodes.PK20.wordLinearMapTranspose_tannerAction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:41:09.252676+00:00
-- url     : https://prove2.me/theorems/f14c14b1-cf43-4d57-bb90-c67266ae5adb
-- title:
--   PK20: word Linear Map Transpose tanner Action
-- statement:
--   Transposition of the quasi-cyclic Tanner matrix is the Tanner action of
--   the star-transposed group-algebra matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalFactor.lean#L103-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalFactor.lean#L103-L128

import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.DistanceBalancing

theorem QEC.Coding.ExpanderCodes.PK20.wordLinearMapTranspose_tannerAction
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    wordLinearMapTranspose (PKDistance.tannerAction A) =
      PKDistance.tannerAction (LiftedProduct.starTranspose A) := by sorry
