-- Prove2me | Theorems.Thm_Rudin_ch11_measurable_ops
-- name    : Rudin.ch11_measurable_ops
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:16:24.993749+00:00
-- url     : https://prove2.me/theorems/1af2c60b-bce5-49b8-8216-772b8d7bf0b8
-- title:
--   Theorems 11.16 and 11.18 — algebraic operations on measurable functions
-- statement:
--   If $f$ and $g$ are measurable real functions, then $|f|$, $f + g$ and $fg$ are measurable.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, pp. 311-312, Theorems 11.16 and 11.18

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorems 11.16 and 11.18: if `f` and `g` are measurable then so are `|f|`, `f + g`
and `f g`. -/
theorem ch11_measurable_ops {X : Type*} [MeasurableSpace X] (f g : X → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => |f x|) ∧ Measurable (fun x => f x + g x) ∧
      Measurable (fun x => f x * g x) := by sorry

end Rudin
