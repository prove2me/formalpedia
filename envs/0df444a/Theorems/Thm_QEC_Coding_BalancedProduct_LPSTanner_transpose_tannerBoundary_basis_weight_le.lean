-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_transpose_tannerBoundary_basis_weight_le
-- name    : QEC.Coding.BalancedProduct.LPSTanner.transpose_tannerBoundary_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:46.251309+00:00
-- url     : https://prove2.me/theorems/3ea5c17c-4bab-4c8b-b5a0-c10ea48661dc
-- title:
--   LPSTanner: transpose tanner Boundary basis weight le
-- statement:
--   Every global Tanner check row touches only the 402 graph edges incident to
--   its vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L762-L799
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L762-L799

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

theorem QEC.Coding.BalancedProduct.LPSTanner.transpose_tannerBoundary_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) (j : Fin 200) :
    HammingWeight
      (wordLinearMapTranspose (tannerBoundary q hq40 hq)
        (canonicalBasisWord (g, j))) ≤ 402 := by sorry
