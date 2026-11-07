-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteDecodedTrace_finset_weighted_residual_traceNorm_le_two_mul_mass
-- name    : QEC.Distillation.FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:39:28.727198+00:00
-- url     : https://prove2.me/theorems/26498837-11ff-4bc2-9ff2-2c28818481a8
-- title:
--   Finite Decoded Trace: finset weighted residual trace Norm le two mul mass
-- statement:
--   A finite nonnegative weighted family whose centered branches are each at
--   trace distance at most two has residual trace norm at most twice its selected
--   weight mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteDecodedTrace.lean#L25-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteDecodedTrace.lean#L25-L51

import Definitions.Def_QEC_Distillation_Core_FiniteCentering
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteDecodedTrace
open Semantics
open scoped BigOperators
universe u v

theorem QEC.Distillation.FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
    {ι : Type u} [DecidableEq ι] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (indices : Finset ι) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected] (branch : ι → Operator H) (center : Operator H)
    (hweight : ∀ i, 0 ≤ weight i)
    (hbranch : ∀ i, traceNorm (branch i - center) ≤ 2) :
    traceNorm (∑ i ∈ indices,
        if selected i then (weight i : Complex) • (branch i - center) else 0) ≤
      ∑ i ∈ indices, if selected i then 2 * weight i else 0 := by sorry
