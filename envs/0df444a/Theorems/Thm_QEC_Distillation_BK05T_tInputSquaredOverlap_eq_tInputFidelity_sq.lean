-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tInputSquaredOverlap_eq_tInputFidelity_sq
-- name    : QEC.Distillation.BK05T.tInputSquaredOverlap_eq_tInputFidelity_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:23:10.746872+00:00
-- url     : https://prove2.me/theorems/fc5d9052-ce34-49eb-b661-6ce83bda91e3
-- title:
--   BK05 T: t Input Squared Overlap eq t Input Fidelity sq
-- statement:
--   The BK05 T construction uses the t Input Squared Overlap eq t Input Fidelity sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L209-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L209-L215

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

theorem QEC.Distillation.BK05T.tInputSquaredOverlap_eq_tInputFidelity_sq
    (rho : DensityOperator QubitSpace) :
    tInputSquaredOverlap rho = tInputFidelity rho ^ 2 := by sorry
