-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qStarBoundary_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qStarBoundary_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:37:20.193194+00:00
-- url     : https://prove2.me/theorems/05d9b7b0-00f6-4e79-b4fc-f67905153200
-- title:
--   BDL26 Tanner Local Regularity: q Star Boundary range eq total Parity ker
-- statement:
--   Binary parity exactness of the connected Q-side cone.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2176-L2180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2176-L2180

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

theorem QEC.Coding.BDL26TannerLocalRegularity.qStarBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (q : P.Q) :
    LinearMap.range (qStarBoundary1 P q) = LinearMap.ker totalParity := by sorry
