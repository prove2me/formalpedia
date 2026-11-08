-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_basis_apply_of_endpoint
-- name    : QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_apply_of_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:30.277212+00:00
-- url     : https://prove2.me/theorems/733d4960-12ae-4419-8072-ba33cba524ef
-- title:
--   LPSTanner: tanner Boundary basis apply of endpoint
-- statement:
--   The LPSTanner construction uses the tanner Boundary basis apply of endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L382-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L382-L395

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

theorem QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_apply_of_endpoint
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq)
    (g : Vertex401 q) (j : Fin 200)
    (hg : g ∈ e.1) :
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j) =
      localCheckCoefficient
        (edgeLocalCoordinate q hq40 hq e g hg) j := by sorry
