-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirl_toOperator_eq_blochProjector_average
-- name    : QEC.Distillation.BK05T.tTwirl_toOperator_eq_blochProjector_average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:24:32.292194+00:00
-- url     : https://prove2.me/theorems/a8e4973d-5dda-47c3-9a72-9c244cb0101b
-- title:
--   BK05 T: t Twirl to Operator eq bloch Projector average
-- statement:
--   For every density given by a Bloch-projector representation, the actual
--   three-branch twirl exactly removes the two transverse Bloch components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L503-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L503-L515

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

theorem QEC.Distillation.BK05T.tTwirl_toOperator_eq_blochProjector_average
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    (tTwirl rho).toOperator = blochProjector (tTwirlBloch r) := by sorry
