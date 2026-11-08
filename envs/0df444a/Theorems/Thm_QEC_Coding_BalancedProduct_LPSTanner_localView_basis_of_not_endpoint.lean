-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_localView_basis_of_not_endpoint
-- name    : QEC.Coding.BalancedProduct.LPSTanner.localView_basis_of_not_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:43.384842+00:00
-- url     : https://prove2.me/theorems/b6aae46c-a0f9-411a-81d2-f80da6b6cd27
-- title:
--   LPSTanner: local View basis of not endpoint
-- statement:
--   The LPSTanner construction uses the local View basis of not endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L314-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L314-L331

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

theorem QEC.Coding.BalancedProduct.LPSTanner.localView_basis_of_not_endpoint
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∉ e.1) :
    localView q hq40 hq g (canonicalBasisWord e) = 0 := by sorry
