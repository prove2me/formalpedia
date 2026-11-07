-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_sum_subtype_eq_sum_of_not_mem_eq_zero
-- name    : QEC.Coding.HypergraphProduct.sum_subtype_eq_sum_of_not_mem_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:28:57.151419+00:00
-- url     : https://prove2.me/theorems/ee5bb788-f8ce-43f9-ab79-5fc2728eb33f
-- title:
--   Hypergraph Product: sum subtype eq sum of not mem eq zero
-- statement:
--   Summing over a finite subtype is the same as summing over the ambient
--   type when every term outside the selected finset vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L51-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L51-L70

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.sum_subtype_eq_sum_of_not_mem_eq_zero
    {I : Type u} {M : Type v}
    [Fintype I] [DecidableEq I] [AddCommMonoid M]
    (A : Finset I) (f : I → M)
    (hzero : ∀ i, i ∉ A → f i = 0) :
    (∑ i : {i // i ∈ A}, f i.1) = ∑ i : I, f i := by sorry
