-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tCanonicalizer_conj_tProjector
-- name    : QEC.Distillation.BK05T.tCanonicalizer_conj_tProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:24:33.063043+00:00
-- url     : https://prove2.me/theorems/4304b01f-32a8-4aa5-a087-7b88a4379d10
-- title:
--   BK05 T: t Canonicalizer conj t Projector
-- statement:
--   The BK05 T construction uses the t Canonicalizer conj t Projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L808-L814
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L808-L814

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

theorem QEC.Distillation.BK05T.tCanonicalizer_conj_tProjector (d : TDirection) :
    (tCanonicalizer d).conjOperator (tProjector d) =
      tProjector tZeroDirection := by sorry
