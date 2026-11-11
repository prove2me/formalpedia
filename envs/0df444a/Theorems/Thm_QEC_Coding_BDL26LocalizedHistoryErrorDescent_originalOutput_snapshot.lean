-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_originalOutput_snapshot
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.originalOutput_snapshot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:07:01.700629+00:00
-- url     : https://prove2.me/theorems/928596ca-2953-4561-a10f-7106d1397f86
-- title:
--   BDL26 Localized History Error Descent: original Output snapshot
-- statement:
--   The BDL26 Localized History Error Descent construction uses the original Output snapshot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L60-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L60-L64

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.originalOutput_snapshot (i : StepIndex n) : originalOutput S n sigma i =
    BDL26CanonicalHistoryMarks.outputAt S n sigma i := by sorry
