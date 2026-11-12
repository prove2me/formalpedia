-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_mapDensity
-- name    : QEC.Distillation.BK05T.tTwirlChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:21:32.509643+00:00
-- url     : https://prove2.me/theorems/c51e3e59-5fc6-42e6-9212-dff015ecc908
-- title:
--   BK05 T: t Twirl Channel map Density
-- statement:
--   The finite-Kraus channel and the explicit random-unitary density twirl
--   coincide on every one-qubit density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L404-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L404-L413

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

theorem QEC.Distillation.BK05T.tTwirlChannel_mapDensity (rho : DensityOperator QubitSpace) :
    tTwirlChannel.mapDensity rho = tTwirl rho := by sorry
