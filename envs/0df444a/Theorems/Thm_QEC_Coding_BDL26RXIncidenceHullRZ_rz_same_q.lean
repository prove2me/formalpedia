-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRZ_rz_same_q
-- name    : QEC.Coding.BDL26RXIncidenceHullRZ.rz_same_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:35:52.832408+00:00
-- url     : https://prove2.me/theorems/43816a2d-f654-44d5-b5f0-e6507952ddc9
-- title:
--   BDL26 RXIncidence Hull RZ: rz same q
-- statement:
--   Original q-cylinder connectivity survives through the genuine Z-local edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRZ.lean#L88-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRZ.lean#L88-L103

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullRZ
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RXIncidenceHullGrowth
open scoped Classical

theorem QEC.Coding.BDL26RXIncidenceHullRZ.rz_same_q (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rzReplacementPresentation P A S) (rzRoot P A S q a) (rzRoot P A S q b) := by sorry
