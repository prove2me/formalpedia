-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_blocklength_eq_edge_add_check
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_blocklength_eq_edge_add_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:00.544269+00:00
-- url     : https://prove2.me/theorems/387abadd-b35f-44e7-9be7-68dcc6f6eb22
-- title:
--   LPSQuotient Tanner: lps Horizontal Subsystem blocklength eq edge add check
-- statement:
--   The actual balanced-product qubit count is the sum of the lifted Tanner
--   edge and check coordinates.  This is the source-repaired finite identity
--   `N = |X₁| + (s - k_L)|X₀|`, before specializing `s = 402` and `k_L = 202`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L659-L669
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L659-L669

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_blocklength_eq_edge_add_check
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit (CyclicGroup q)) =
      Fintype.card (Edge401 q hq) + Fintype.card (Check401 q) := by sorry
