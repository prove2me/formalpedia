-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_checkBlock_basis_of_ne
-- name    : QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:22.611783+00:00
-- url     : https://prove2.me/theorems/35f08f44-fd4a-4dcf-9269-7256f8b6a1ce
-- title:
--   LPSTanner: check Block basis of ne
-- statement:
--   The LPSTanner construction uses the check Block basis of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L661-L670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L661-L670

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

theorem QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_of_ne
    (q : ℕ) (g w : Vertex401 q) (j : Fin 200)
    (hwg : w ≠ g) :
    checkBlock q w (canonicalBasisWord (g, j)) = 0 := by sorry
