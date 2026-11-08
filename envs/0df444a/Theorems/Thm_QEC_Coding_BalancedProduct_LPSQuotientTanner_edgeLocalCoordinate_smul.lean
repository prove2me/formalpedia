-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_edgeLocalCoordinate_smul
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.edgeLocalCoordinate_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:06.481525+00:00
-- url     : https://prove2.me/theorems/eb273d74-da12-486b-9885-de5a737ddf68
-- title:
--   LPSQuotient Tanner: edge Local Coordinate smul
-- statement:
--   Right multiplication preserves the generator label, hence also the fixed
--   local-code coordinate, of every incident half-edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L203-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L203-L253

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.edgeLocalCoordinate_smul
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    edgeLocalCoordinate q hq40 hq (h • e) (h • g)
        ((mem_smul_edge_iff q hq h e g).2 hg) =
      edgeLocalCoordinate q hq40 hq e g hg := by sorry
