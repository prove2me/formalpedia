-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_shared_z_roots
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_shared_z_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:02:48.243398+00:00
-- url     : https://prove2.me/theorems/86e2b725-9726-4424-b8b6-0a94a08aead4
-- title:
--   BDL26 RXIncidence Hull Successors: rx shared z roots
-- statement:
--   A shared old Z gives a genuine path between any two retained root copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L99-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L99-L111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_shared_z_roots (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q r : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (hrz : P.qz r z = true) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rxReplacementPresentation P S) (rxRoot P S q a) (rxRoot P S r b) := by sorry
