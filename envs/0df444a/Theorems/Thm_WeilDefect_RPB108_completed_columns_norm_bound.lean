-- Prove2me | Theorems.Thm_WeilDefect_RPB108_completed_columns_norm_bound
-- name    : WeilDefect.RPB108.completed_columns_norm_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:01.390103+00:00
-- url     : https://prove2.me/theorems/a0e30298-4c38-4dfb-8836-ea0db6f5416b
-- title:
--   Completed columns norm bound
-- statement:
--   In every normed additive commutative group $E$ equipped with a complex normed vector-space structure, with no completeness assumption, let $v_0,v_1,v_2,v_3\in E$ and real numbers $b_0,b_1,b_2,b_3$ satisfy $\|v_i\|\le b_i$ at every index. For every four complex scalars $z_i$ and every $h\in E$, $\|\sum_{i=0}^3z_i v_i+h\|\le\sum_{i=0}^3b_i\|z_i\|+\|h\|$. Here $z_i v_i$ denotes complex scalar multiplication; the norm hypotheses force $b_i\ge0$, and there are no restrictions on the complex coefficients or on $h$, including zero values.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; CompletedColumns.lean, line 30; SHA256 79e8e4bde2ec62b81ab4dc5b861c03619ff6006496bc610ff2ad24be9d84405e. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.completed_columns_norm_bound in WeilDefect/RPB108/CompletedColumns.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 79e8e4bde2ec62b81ab4dc5b861c03619ff6006496bc610ff2ad24be9d84405e). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.completed_columns_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : Fin 4 → E) (b : Fin 4 → ℝ) (hv : ∀ i, ‖v i‖ ≤ b i)
    (z : Fin 4 → ℂ) (h : E) :
    ‖(∑ i, z i • v i) + h‖ ≤ (∑ i, b i * ‖z i‖) + ‖h‖ := by sorry
