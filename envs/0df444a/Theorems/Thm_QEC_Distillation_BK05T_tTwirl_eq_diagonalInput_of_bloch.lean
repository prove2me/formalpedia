-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirl_eq_diagonalInput_of_bloch
-- name    : QEC.Distillation.BK05T.tTwirl_eq_diagonalInput_of_bloch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:21:28.152138+00:00
-- url     : https://prove2.me/theorems/b849d52d-4dde-4806-b0fd-d1aa6294815e
-- title:
--   BK05 T: t Twirl eq diagonal Input of bloch
-- statement:
--   The generic Bloch twirl equality is an equality to the concrete BK05
--   diagonal T0/T1 mixture whenever their displayed Bloch vectors agree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L573-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L573-L582

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

theorem QEC.Distillation.BK05T.tTwirl_eq_diagonalInput_of_bloch
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r)
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hdiagonal : tTwirlBloch r = tDiagonalBloch epsilon) :
    tTwirl rho = tDiagonalInput epsilon hzero hone := by sorry
