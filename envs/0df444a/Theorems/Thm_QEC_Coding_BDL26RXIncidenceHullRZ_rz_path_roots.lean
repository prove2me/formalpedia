-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRZ_rz_path_roots
-- name    : QEC.Coding.BDL26RXIncidenceHullRZ.rz_path_roots
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T02:37:30.131198+00:00
-- url     : https://prove2.me/theorems/8005da80-a275-4bac-ba96-27c03d2e28a0
-- title:
--   BDL26 RXIncidence Hull RZ: rz path roots
-- statement:
--   Any actual original shared-Z path lifts, including independently chosen copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRZ.lean#L184-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRZ.lean#L184-L191

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRZ
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RXIncidenceHullGrowth
open scoped Classical

theorem QEC.Coding.BDL26RXIncidenceHullRZ.rz_path_roots (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) {q r : P.Q} (path : SharedZPath P q r) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q a) (rzRoot P A S r b) := by sorry
