-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_basis_apply
-- name    : QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:38.174322+00:00
-- url     : https://prove2.me/theorems/6360e8b1-ff27-4523-b009-942087147808
-- title:
--   LPSTanner: tanner Boundary basis apply
-- statement:
--   Coordinate form of BE20's defining equation: a basis edge contributes
--   at an endpoint exactly the local parity-check column selected by that
--   half-edge label, and contributes zero at every non-endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L366-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L366-L380

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

theorem QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_apply
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq)
    (g : Vertex401 q) (j : Fin 200) :
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j) =
      if hg : g ∈ e.1 then
        localCheckCoefficient (edgeLocalCoordinate q hq40 hq e g hg) j
      else 0 := by sorry
