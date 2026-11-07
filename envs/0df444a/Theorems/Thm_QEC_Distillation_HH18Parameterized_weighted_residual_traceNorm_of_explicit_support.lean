-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_weighted_residual_traceNorm_of_explicit_support
-- name    : QEC.Distillation.HH18Parameterized.weighted_residual_traceNorm_of_explicit_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:08:52.924416+00:00
-- url     : https://prove2.me/theorems/3bf83101-4470-40aa-a096-cc6f4edd75e1
-- title:
--   HH18 Parameterized: weighted residual trace Norm of explicit support
-- statement:
--   Bound the trace norm of an explicitly selected centered residual by twice
--   its selected real mass, delegating the pointwise finite estimate to
--   `FiniteDecodedTrace`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L81-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L81-L106

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u v w

theorem QEC.Distillation.HH18Parameterized.weighted_residual_traceNorm_of_explicit_support
    {ι : Type u} [DecidableEq ι] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (support : Finset ι) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected] (branch : ι → Operator H) (center : Operator H)
    (residual : Operator H) (residualMass : ℝ)
    (hresidual : residual = support.sum (fun i =>
      if selected i then (weight i : Complex) • (branch i - center) else 0))
    (hmass : residualMass = support.sum (fun i =>
      if selected i then weight i else 0))
    (hweight : ∀ i, 0 ≤ weight i)
    (hbranch : ∀ i, traceNorm (branch i - center) ≤ 2) :
    traceNorm residual ≤ 2 * residualMass := by sorry
