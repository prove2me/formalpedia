-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_mapDensity_canonicalizedInput
-- name    : QEC.Distillation.BK05T.tTwirlChannel_mapDensity_canonicalizedInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:36:08.472576+00:00
-- url     : https://prove2.me/theorems/61324a26-72e5-46a6-82cc-b942808bd65a
-- title:
--   BK05 T: t Twirl Channel map Density canonicalized Input
-- statement:
--   Finite Clifford normalization followed by the physical T twirl produces
--   the exact BK05 diagonal T0/T1 mixture at error `1 - F_T(rho)^2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L843-L856
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L843-L856

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

theorem QEC.Distillation.BK05T.tTwirlChannel_mapDensity_canonicalizedInput
    (rho : DensityOperator QubitSpace) :
    tTwirlChannel.mapDensity (tCanonicalizedInput rho) =
      tDiagonalInput (1 - tFidelity rho ^ 2)
        (tCanonicalizedInput_error_mem_Icc_half rho).1
        ((tCanonicalizedInput_error_mem_Icc_half rho).2.trans (by norm_num)) := by sorry
