-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_xBoundary_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26TannerLocalRegularity.xBoundary_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:31:30.963194+00:00
-- url     : https://prove2.me/theorems/725097e6-876c-4f9e-a077-67f09a6c53fc
-- title:
--   BDL26 Tanner Local Regularity: x Boundary range eq total Parity ker
-- statement:
--   Exactness of every admissible X-star boundary is theorem-derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1106-L1112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1106-L1112

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u

theorem QEC.Coding.BDL26TannerLocalRegularity.xBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    LinearMap.range (graphBoundary (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)) =
      LinearMap.ker totalParity := by sorry
