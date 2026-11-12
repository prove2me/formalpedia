-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelope_closedForm
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_closedForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:27:48.481047+00:00
-- url     : https://prove2.me/theorems/8953f2ce-2070-4062-b57a-ac414e3c0aa0
-- title:
--   BH12 Concatenation: bh12 Quadratic Envelope closed Form
-- statement:
--   The quadratic envelope has an exact finite-depth form after multiplication
--   by the positive BH12 coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1707-L1723
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1707-L1723

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_closedForm (q : Nat) (p : ErrorParameter)
    (z : Nat) :
    quadraticCoefficient q * bh12QuadraticEnvelope q p z =
      (quadraticCoefficient q * p.rate) ^ (2 ^ z) := by sorry
