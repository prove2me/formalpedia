-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_eq_diagonalInput_of_bloch
-- name    : QEC.Distillation.BK05T.tTwirlChannel_eq_diagonalInput_of_bloch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:32:02.167572+00:00
-- url     : https://prove2.me/theorems/1d75e22b-75ee-45af-96c8-ac38c21f2573
-- title:
--   BK05 T: t Twirl Channel eq diagonal Input of bloch
-- statement:
--   The same diagonalization statement for the finite-Kraus CPTP channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L585-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L585-L592

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

theorem QEC.Distillation.BK05T.tTwirlChannel_eq_diagonalInput_of_bloch
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r)
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hdiagonal : tTwirlBloch r = tDiagonalBloch epsilon) :
    tTwirlChannel.mapDensity rho = tDiagonalInput epsilon hzero hone := by sorry
