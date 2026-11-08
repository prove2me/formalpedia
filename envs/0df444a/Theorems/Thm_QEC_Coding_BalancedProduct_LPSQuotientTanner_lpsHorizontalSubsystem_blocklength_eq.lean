-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_blocklength_eq
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_blocklength_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:26.562955+00:00
-- url     : https://prove2.me/theorems/b44eebd1-00e7-482b-a6a2-92c7d92a5ca2
-- title:
--   LPSQuotient Tanner: lps Horizontal Subsystem blocklength eq
-- statement:
--   For the concrete BE20 local code `[402,202,≥41]`, the corrected exact
--   blocklength is `N = 201|X₀| + 200|X₀| = 401|X₀|`.  No source or spectral
--   premise is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L674-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L674-L685

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_blocklength_eq
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit (CyclicGroup q)) =
      401 * Fintype.card (Vertex401 q) := by sorry
