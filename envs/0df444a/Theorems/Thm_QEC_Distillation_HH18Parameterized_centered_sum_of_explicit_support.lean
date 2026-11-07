-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_centered_sum_of_explicit_support
-- name    : QEC.Distillation.HH18Parameterized.centered_sum_of_explicit_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:24.779078+00:00
-- url     : https://prove2.me/theorems/bb441b60-7e26-4490-85b3-4e3f16a86f41
-- title:
--   HH18 Parameterized: centered sum of explicit support
-- statement:
--   Center one explicitly selected finite family at its distinguished zero
--   branch, delegating the algebra to `FiniteCentering`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L60-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L60-L76

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

theorem QEC.Distillation.HH18Parameterized.centered_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] {R : Type v} [Semiring R] {M : Type w}
    [AddCommGroup M] [Module R M]
    (support : Finset ι) (weight : ι → R) (accepts : ι → Prop)
    [DecidablePred accepts] (branch : ι → M) (zeroIndex : ι)
    (center raw residual : M) (mass : R)
    (hraw : raw = support.sum (fun i =>
      if accepts i then weight i • branch i else 0))
    (hmass : mass = support.sum (fun i =>
      if accepts i then weight i else 0))
    (hresidual : residual = support.sum (fun i =>
      if accepts i ∧ i ≠ zeroIndex then weight i • (branch i - center) else 0))
    (hzero : branch zeroIndex = center) :
    raw - mass • center = residual := by sorry
