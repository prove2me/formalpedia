-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_edge401_eq_cyclic_mul_edgeOrbit
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.card_edge401_eq_cyclic_mul_edgeOrbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:23.883499+00:00
-- url     : https://prove2.me/theorems/c6739990-890f-4341-84e9-650c111b6477
-- title:
--   LPSQuotient Tanner: card edge401 eq cyclic mul edge Orbit
-- statement:
--   The actual LPS edge set is the free cyclic cover of its edge-orbit set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L581-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L581-L593

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
set_option maxRecDepth 4000

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.card_edge401_eq_cyclic_mul_edgeOrbit
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    Fintype.card (Edge401 q hq) =
      q * Fintype.card (EdgeOrbit401 q hq) := by sorry
