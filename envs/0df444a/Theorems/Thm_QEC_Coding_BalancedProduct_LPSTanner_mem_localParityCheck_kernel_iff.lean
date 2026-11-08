-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_mem_localParityCheck_kernel_iff
-- name    : QEC.Coding.BalancedProduct.LPSTanner.mem_localParityCheck_kernel_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:43.703195+00:00
-- url     : https://prove2.me/theorems/8e042181-d0cd-4d19-9af9-842211f9dcaa
-- title:
--   LPSTanner: mem local Parity Check kernel iff
-- statement:
--   The concrete local parity check has exactly the already-proved GV+ code
--   as its kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L74-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L74-L94

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

theorem QEC.Coding.BalancedProduct.LPSTanner.mem_localParityCheck_kernel_iff
    (w : Word (ZMod 2) LocalCoordinate) :
    w ∈ (parityCheckKernelCode localParityCheck).carrier ↔
      w ∈ localCode.carrier := by sorry
