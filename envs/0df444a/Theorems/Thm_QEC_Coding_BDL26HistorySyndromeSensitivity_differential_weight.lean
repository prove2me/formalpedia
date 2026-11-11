-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_differential_weight
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.differential_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:57:54.203204+00:00
-- url     : https://prove2.me/theorems/acfb3436-b7d2-4332-b108-8671201df558
-- title:
--   BDL26 History Syndrome Sensitivity: differential weight
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the differential weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L50-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L50-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.differential_weight (e : (indexedFamily S d).Cochain1 i.succ) :
    HammingWeight ((indexedFamily S d).coboundary1 i.succ e) ≤ 4 * HammingWeight e := by sorry
