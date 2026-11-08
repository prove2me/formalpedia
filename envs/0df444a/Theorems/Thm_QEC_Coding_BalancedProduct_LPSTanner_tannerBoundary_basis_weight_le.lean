-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_basis_weight_le
-- name    : QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:48.593556+00:00
-- url     : https://prove2.me/theorems/33766099-6322-486c-8abe-6c10c4357b78
-- title:
--   LPSTanner: tanner Boundary basis weight le
-- statement:
--   Every global edge column is supported on 200 checks at each of its two
--   endpoints, hence has weight at most 400.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L412-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L412-L450

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

theorem QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) :
    HammingWeight (tannerBoundary q hq40 hq (canonicalBasisWord e)) ≤ 400 := by sorry
