-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_adjacent_potential_pair
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.adjacent_potential_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:04:20.888937+00:00
-- url     : https://prove2.me/theorems/be801399-5b30-4e9f-8eda-2a3478013ccf
-- title:
--   BDL26 Localized History Error Descent: adjacent potential pair
-- statement:
--   Every adjacent pair retains exactly p+FZ.map0(q), with no gauge substitution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L555-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L555-L570

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.adjacent_potential_pair (i j : StepIndex n) (hij : j.succ=i.castSucc) :
    intervalPotential S n sigma tau top j.castSucc i.succ=
      edgePotential S n sigma tau top i+
        ((Data S n).selectedMap i).map0 (hij ▸ edgePotential S n sigma tau top j) := by sorry
