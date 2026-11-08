-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qSubdivisionBoundary_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qSubdivisionBoundary_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:37:05.217171+00:00
-- url     : https://prove2.me/theorems/7bb99e2d-379e-4ddb-b42d-8a438f3fcb42
-- title:
--   BDL26 Tanner Local Regularity: q Subdivision Boundary range eq total Parity ker
-- statement:
--   Binary parity exactness for the explicitly connected Q subdivision.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2761-L2767
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2761-L2767

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

theorem QEC.Coding.BDL26TannerLocalRegularity.qSubdivisionBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    LinearMap.range (qSubdivisionBoundary1 P q S) =
      LinearMap.ker totalParity := by sorry
