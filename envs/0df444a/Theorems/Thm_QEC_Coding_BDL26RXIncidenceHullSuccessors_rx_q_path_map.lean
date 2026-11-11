-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullSuccessors_rx_q_path_map
-- name    : QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_path_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T08:59:38.659594+00:00
-- url     : https://prove2.me/theorems/9156ef0c-63b8-419c-89a6-8715fd99517f
-- title:
--   BDL26 RXIncidence Hull Successors: rx q path map
-- statement:
--   The constructive local cylinder path induces a path of actual successor
--   Q coordinates sharing actual successor Z checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L44-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean#L44-L59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

theorem QEC.Coding.BDL26RXIncidenceHullSuccessors.rx_q_path_map (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    {u v : QDoubleCylinderVertex P q S}
    (path : UndirectedPath (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) u v) :
    SharedZPath (rxReplacementPresentation P S) (Sum.inr ⟨q,u⟩) (Sum.inr ⟨q,v⟩) := by sorry
