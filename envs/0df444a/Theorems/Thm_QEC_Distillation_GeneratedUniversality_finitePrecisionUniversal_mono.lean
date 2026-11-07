-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_finitePrecisionUniversal_mono
-- name    : QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:09:50.452884+00:00
-- url     : https://prove2.me/theorems/afcfee61-ebbe-4048-b390-ce516e3f5d7d
-- title:
--   Generated Universality: finite Precision Universal mono
-- statement:
--   Finite-precision universality is monotone under enlarging the generating set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L280-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L280-L286

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

theorem QEC.Distillation.GeneratedUniversality.finitePrecisionUniversal_mono {n : Type u} [Fintype n] [DecidableEq n]
    {generators generators' : Set (UnitaryGate n)}
    (h : generators ⊆ generators')
    (huniversal : FinitePrecisionUniversal generators) :
    FinitePrecisionUniversal generators' := by sorry
