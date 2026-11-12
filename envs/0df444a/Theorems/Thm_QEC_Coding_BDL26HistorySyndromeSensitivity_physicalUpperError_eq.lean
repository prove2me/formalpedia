-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_physicalUpperError_eq
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.physicalUpperError_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:29:02.775008+00:00
-- url     : https://prove2.me/theorems/75777dd1-848f-4771-b9f4-68e4e0c66042
-- title:
--   BDL26 History Syndrome Sensitivity: physical Upper Error eq
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the physical Upper Error eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L70-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L70-L72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.physicalUpperError_eq (i : StepIndex n)
    (e : (SuffixData S n).family.Cochain1 i.succ) :
    physicalUpperError S n i e = e := by sorry
