-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_finitePrecisionRegisterUniversal_of_dense
-- name    : QEC.Distillation.GeneratedUniversality.finitePrecisionRegisterUniversal_of_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:10:03.295952+00:00
-- url     : https://prove2.me/theorems/c69b0d1b-b047-475a-8d2a-91bd17dcd633
-- title:
--   Generated Universality: finite Precision Register Universal of dense
-- statement:
--   Density entails the finite-register finite-precision interface.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L313-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L313-L317

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise

theorem QEC.Distillation.GeneratedUniversality.finitePrecisionRegisterUniversal_of_dense (r : Nat)
    {generators : Set (UnitaryGate (Fin (2 ^ r)))}
    (hdense : GeneratedUnitaryDense generators) :
    FinitePrecisionRegisterUniversal r generators := by sorry
