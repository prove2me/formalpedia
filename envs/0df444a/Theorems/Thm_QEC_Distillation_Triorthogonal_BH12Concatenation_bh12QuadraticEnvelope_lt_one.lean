-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelope_lt_one
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:28:23.045558+00:00
-- url     : https://prove2.me/theorems/64f06633-18a8-43da-af10-74ab60fd537f
-- title:
--   BH12 Concatenation: bh12 Quadratic Envelope lt one
-- statement:
--   The explicit positive/small-rate assumptions make each finite quadratic
--   envelope a genuine number strictly between zero and one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1769-L1793
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1769-L1793

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12QuadraticEnvelope_lt_one (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    ∀ z : Nat, bh12QuadraticEnvelope q p z < 1 := by sorry
