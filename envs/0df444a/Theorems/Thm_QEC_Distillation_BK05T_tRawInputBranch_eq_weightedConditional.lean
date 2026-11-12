-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tRawInputBranch_eq_weightedConditional
-- name    : QEC.Distillation.BK05T.tRawInputBranch_eq_weightedConditional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:29:34.622229+00:00
-- url     : https://prove2.me/theorems/4e8d14ef-2117-456a-86a6-7686ed1e33e9
-- title:
--   BK05 T: t Raw Input Branch eq weighted Conditional
-- statement:
--   The BK05 T construction uses the t Raw Input Branch eq weighted Conditional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L71-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L71-L76

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators

theorem QEC.Distillation.BK05T.tRawInputBranch_eq_weightedConditional (epsilon : Real) (word : Fin 2)
    (hpositive : 0 < tInputWeight epsilon word) :
    tRawInputBranch epsilon word =
      (tInputWeight epsilon word : Complex) •
        (tInputConditional epsilon word hpositive).toOperator := by sorry
