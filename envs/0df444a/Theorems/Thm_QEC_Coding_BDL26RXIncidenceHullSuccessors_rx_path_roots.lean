-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_path_roots
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_path_roots
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:01:45.152615+00:00
-- url     : https://prove2.me/theorems/f2166f90-e58d-4bec-8d0c-650bc12b8c63
-- title:
--   BDL26 RXIncidence Hull Successors: rx path roots
-- statement:
--   Every original component path lifts while each old Q supplies BOTH
--   retained copies, without assuming connectivity of the entire successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L115-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L115-L121

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_path_roots (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) {q r : P.Q} (path : SharedZPath P q r) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rxReplacementPresentation P S) (rxRoot P S q a) (rxRoot P S r b) := by sorry
