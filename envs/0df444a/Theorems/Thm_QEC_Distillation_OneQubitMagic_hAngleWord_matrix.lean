-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleWord_matrix
-- name    : QEC.Distillation.OneQubitMagic.hAngleWord_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:05:22.857141+00:00
-- url     : https://prove2.me/theorems/6993e459-4bfa-49fb-85b1-2cb91626bea3
-- title:
--   One Qubit Magic: h Angle Word matrix
-- statement:
--   Exact concrete matrix of the H-route word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L143-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean#L143-L161

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.hAngleWord_matrix :
    (hAngleWord : SingleQubitMatrix) =
      !![(3 : Complex) / 4 + Complex.I * ((Real.sqrt 2 - 1 : Real) / 4),
         -(1 : Complex) / 4 + Complex.I * ((1 + Real.sqrt 2 : Real) / 4);
         (1 : Complex) / 4 + Complex.I * ((1 + Real.sqrt 2 : Real) / 4),
         (3 : Complex) / 4 + Complex.I * ((1 - Real.sqrt 2 : Real) / 4)] := by sorry
