-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelope_pos
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:25:33.151277+00:00
-- url     : https://prove2.me/theorems/cf3b65fa-961b-43f9-a04f-a85b1948c2cc
-- title:
--   BH12 Concatenation: bh12 Quadratic Envelope pos
-- statement:
--   A positive initial error rate makes every finite quadratic envelope
--   positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1727-L1735
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1727-L1735

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_pos (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) :
    ∀ z : Nat, 0 < bh12QuadraticEnvelope q p z := by sorry
