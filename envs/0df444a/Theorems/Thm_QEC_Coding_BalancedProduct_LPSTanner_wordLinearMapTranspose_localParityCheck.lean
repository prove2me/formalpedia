-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_wordLinearMapTranspose_localParityCheck
-- name    : QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_localParityCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:55.199196+00:00
-- url     : https://prove2.me/theorems/04413e45-a831-4e48-95a2-24f11b0de9cd
-- title:
--   LPSTanner: word Linear Map Transpose local Parity Check
-- statement:
--   The transpose of the reconstructed parity check is not an abstract row
--   space: it is exactly the complementary systematic dual encoding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L488-L499
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L488-L499

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype

theorem QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_localParityCheck
    (y : Word (ZMod 2) (Fin 200)) :
    wordLinearMapTranspose localParityCheck y =
      systematicDualEncode localMatrix y := by sorry
