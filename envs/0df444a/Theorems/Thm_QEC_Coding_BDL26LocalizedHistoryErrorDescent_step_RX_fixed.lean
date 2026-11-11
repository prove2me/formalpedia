-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_RX_fixed
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RX_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:08:35.022779+00:00
-- url     : https://prove2.me/theorems/e38c7eb5-cb09-4751-afdc-e4ffd5c8404f
-- title:
--   BDL26 Localized History Error Descent: step RX fixed
-- statement:
--   RX interior windows retain the actual some-parent and fixed normalized
--   root and full potential; the seven-clause theorem remains directly usable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L716-L727
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L716-L727

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RX_fixed (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    (step S n sigma tau i u).lower.word=
      BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u) ∧
    (step S n sigma tau i u).potential=
      BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u) ∧
    parent S ((Edge n i).val+1) (Vertex.x u.center)=
      some (Vertex.x (step S n sigma tau i u).lower.center) := by sorry
