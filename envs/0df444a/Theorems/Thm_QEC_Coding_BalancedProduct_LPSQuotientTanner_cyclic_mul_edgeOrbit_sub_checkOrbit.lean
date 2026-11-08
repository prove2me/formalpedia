-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_cyclic_mul_edgeOrbit_sub_checkOrbit
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.cyclic_mul_edgeOrbit_sub_checkOrbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:42:44.206119+00:00
-- url     : https://prove2.me/theorems/77cb238a-563a-46e2-a71a-ff9c8b48cf1d
-- title:
--   LPSQuotient Tanner: cyclic mul edge Orbit sub check Orbit
-- statement:
--   The orbit-rank lower bound is exactly of order `|X₀|/q`: multiplying
--   the edge-orbit/check-orbit difference by the free-orbit size recovers the
--   number of LPS vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L932-L944
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L932-L944

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.cyclic_mul_edgeOrbit_sub_checkOrbit
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    q * (Fintype.card (EdgeOrbit401 q hq) -
        Fintype.card (CheckOrbit401 q)) =
      Fintype.card (Vertex401 q) := by sorry
