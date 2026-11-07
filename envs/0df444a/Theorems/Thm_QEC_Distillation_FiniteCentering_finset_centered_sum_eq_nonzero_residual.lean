-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteCentering_finset_centered_sum_eq_nonzero_residual
-- name    : QEC.Distillation.FiniteCentering.finset_centered_sum_eq_nonzero_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:39:07.433411+00:00
-- url     : https://prove2.me/theorems/5860a80a-a889-44b5-b39d-0cf3233a8314
-- title:
--   Finite Centering: finset centered sum eq nonzero residual
-- statement:
--   Centering an accepted finite family at its zero branch leaves exactly the
--   accepted nonzero residual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteCentering.lean#L21-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/FiniteCentering.lean#L21-L39

import Mathlib.Algebra.Module.BigOperators
import Definitions.Def_QEC_Distillation_Core_FiniteCentering
set_option autoImplicit false
universe u v w
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteCentering
open scoped BigOperators

theorem QEC.Distillation.FiniteCentering.finset_centered_sum_eq_nonzero_residual
    {ι : Type u} [DecidableEq ι] {R : Type v} [Semiring R] {M : Type w}
    [AddCommGroup M] [Module R M]
    (indices : Finset ι) (weight : ι → R) (accepts : ι → Prop)
    [DecidablePred accepts] (branch : ι → M) (zeroIndex : ι) (center : M)
    (hzero : branch zeroIndex = center) :
    (∑ i ∈ indices, if accepts i then weight i • branch i else 0) -
        (∑ i ∈ indices, if accepts i then weight i else 0) • center =
      ∑ i ∈ indices,
        if accepts i ∧ i ≠ zeroIndex then weight i • (branch i - center) else 0 := by sorry
