-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tInputSquaredOverlap_eq_bloch_sum
-- name    : QEC.Distillation.BK05T.tInputSquaredOverlap_eq_bloch_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:24:23.09528+00:00
-- url     : https://prove2.me/theorems/5107d379-7a43-4448-b023-eb2da7b0f2ae
-- title:
--   BK05 T: t Input Squared Overlap eq bloch sum
-- statement:
--   The distinguished T0 overlap is the affine sum of the input Bloch
--   coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L519-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L519-L551

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

theorem QEC.Distillation.BK05T.tInputSquaredOverlap_eq_bloch_sum
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r) :
    tInputSquaredOverlap rho =
      (1 + (r .x + r .y + r .z) / Real.sqrt 3) / 2 := by sorry
