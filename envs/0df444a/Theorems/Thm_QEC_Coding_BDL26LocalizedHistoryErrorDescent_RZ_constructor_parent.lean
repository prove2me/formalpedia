-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_RZ_constructor_parent
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.RZ_constructor_parent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:22:16.030785+00:00
-- url     : https://prove2.me/theorems/ff044b2c-b030-4d7c-b567-ca3000c5abd5
-- title:
--   BDL26 Localized History Error Descent: RZ constructor parent
-- statement:
--   Exact raw parent table, including none for both positive-dimensional
--   constructors. A computed star centre is not relabelled as a graph parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L692-L697
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L692-L697

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.RZ_constructor_parent (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (v : BDL26RZLocalReplacement.RZX (state S (Edge n i).val).presentation S) :
    parent S ((Edge n i).val+1)
      (Vertex.x (BDL26RZPhysicalXStarTransport.upperXChart S (n+2) (Edge n i) h v))=
      BDL26RZPhysicalXStarTransport.rawParent (state S (Edge n i).val).presentation S v := by sorry
