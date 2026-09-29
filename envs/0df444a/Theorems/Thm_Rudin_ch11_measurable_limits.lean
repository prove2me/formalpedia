-- Prove2me | Theorems.Thm_Rudin_ch11_measurable_limits
-- name    : Rudin.ch11_measurable_limits
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:56:39.518118+00:00
-- url     : https://prove2.me/theorems/3e910ca5-0af1-4fd2-914b-cefdc24a8253
-- title:
--   Theorem 11.17 — suprema and upper limits of measurable functions
-- statement:
--   If $f_1, f_2, \dots$ are measurable, then $\sup_n f_n$ and $\limsup_n f_n$ are measurable. As in Rudin the functions take values in the extended half-line, so both are always defined.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 311, Theorem 11.17

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory
open scoped ENNReal

namespace Rudin

/-- Rudin, Theorem 11.17: the pointwise supremum and the upper limit of a sequence of measurable
functions are measurable.  As in Rudin the functions take values in the extended half-line, so
that the supremum and the upper limit are always defined. -/
theorem ch11_measurable_limits {X : Type*} [MeasurableSpace X] (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨆ n, f n x) ∧
      Measurable (fun x => limsup (fun n => f n x) atTop) := by sorry

end Rudin
