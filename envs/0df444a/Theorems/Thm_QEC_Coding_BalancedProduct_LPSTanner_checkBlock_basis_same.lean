-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_checkBlock_basis_same
-- name    : QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:22.457962+00:00
-- url     : https://prove2.me/theorems/90b21291-6aaa-46f2-964a-7a09d06ea838
-- title:
--   LPSTanner: check Block basis same
-- statement:
--   The LPSTanner construction uses the check Block basis same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L647-L659
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L647-L659

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

theorem QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_same
    (q : ℕ) (g : Vertex401 q) (j : Fin 200) :
    checkBlock q g (canonicalBasisWord (g, j)) =
      canonicalBasisWord j := by sorry
