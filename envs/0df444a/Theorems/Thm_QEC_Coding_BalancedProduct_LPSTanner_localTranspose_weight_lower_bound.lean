-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_localTranspose_weight_lower_bound
-- name    : QEC.Coding.BalancedProduct.LPSTanner.localTranspose_weight_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:32.590001+00:00
-- url     : https://prove2.me/theorems/fd9e0c0a-b5ac-4e24-8c72-361df31bcc48
-- title:
--   LPSTanner: local Transpose weight lower bound
-- statement:
--   Every nonzero local check combination touches at least 41 incident
--   variables, by the already-proved genuine dual distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L503-L507
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L503-L507

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

theorem QEC.Coding.BalancedProduct.LPSTanner.localTranspose_weight_lower_bound
    (y : Word (ZMod 2) (Fin 200)) (hy : y ≠ 0) :
    41 ≤ HammingWeight (wordLinearMapTranspose localParityCheck y) := by sorry
