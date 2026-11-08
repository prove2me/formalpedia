-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_zBoundary_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26TannerLocalRegularity.zBoundary_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:35:55.594207+00:00
-- url     : https://prove2.me/theorems/9da6d525-83e9-43d9-aa42-a0f9fcfffb24
-- title:
--   BDL26 Tanner Local Regularity: z Boundary range eq total Parity ker
-- statement:
--   Exactness of every admissible Z-star boundary is theorem-derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1115-L1121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1115-L1121

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

theorem QEC.Coding.BDL26TannerLocalRegularity.zBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (z : P.Z) :
    LinearMap.range (graphBoundary (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)) =
      LinearMap.ker totalParity := by sorry
