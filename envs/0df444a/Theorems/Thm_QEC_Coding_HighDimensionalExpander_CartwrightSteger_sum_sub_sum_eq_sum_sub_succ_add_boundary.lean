-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sum_sub_sum_eq_sum_sub_succ_add_boundary
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.sum_sub_sum_eq_sum_sub_succ_add_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:48.595959+00:00
-- url     : https://prove2.me/theorems/d9818324-ceb0-4d88-8d6a-12683590af79
-- title:
--   Cartwright Steger: sum sub sum eq sum sub succ add boundary
-- statement:
--   A finite telescoping identity that retains both boundary terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L997-L1015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L997-L1015

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.sum_sub_sum_eq_sum_sub_succ_add_boundary
    {A : Type*} [AddCommGroup A] (L D : ℕ → A) (n : ℕ) :
    (∑ i ∈ Finset.range n, L i) - (∑ i ∈ Finset.range n, D i) =
      (∑ i ∈ Finset.range n, (L i - D (i + 1))) + D n - D 0 := by sorry
