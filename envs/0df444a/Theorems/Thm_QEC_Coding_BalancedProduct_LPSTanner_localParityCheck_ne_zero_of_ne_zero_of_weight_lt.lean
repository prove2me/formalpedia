-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_localParityCheck_ne_zero_of_ne_zero_of_weight_lt
-- name    : QEC.Coding.BalancedProduct.LPSTanner.localParityCheck_ne_zero_of_ne_zero_of_weight_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:08.767887+00:00
-- url     : https://prove2.me/theorems/985d2175-a02a-4490-8b43-77fb3d41423a
-- title:
--   LPSTanner: local Parity Check ne zero of ne zero of weight lt
-- statement:
--   A nonzero local word below the proved distance 41 cannot satisfy every
--   local check.  This is the local algebraic input to the Sipser--Spielman/BE20
--   small-set expansion argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L512-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L512-L524

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

theorem QEC.Coding.BalancedProduct.LPSTanner.localParityCheck_ne_zero_of_ne_zero_of_weight_lt
    (w : Word (ZMod 2) LocalCoordinate)
    (hw0 : w ≠ 0)
    (hw : HammingWeight w < 41) :
    localParityCheck w ≠ 0 := by sorry
