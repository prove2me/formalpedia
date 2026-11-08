-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderBoundary_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderBoundary_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:00.115497+00:00
-- url     : https://prove2.me/theorems/a8d82e56-6039-4e36-8f11-a180a529d6d0
-- title:
--   BDL26 Tanner Local Regularity: q Double Cylinder Boundary range eq total Parity ker
-- statement:
--   Binary parity exactness for the connected Q-side double cylinder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3099-L3106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3099-L3106

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

theorem QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderBoundary_range_eq_totalParity_ker
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) :
    LinearMap.range (qDoubleCylinderBoundary1 P q S) =
      LinearMap.ker totalParity := by sorry
