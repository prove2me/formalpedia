-- Prove2me | Theorems.Thm_Rudin_ch11_integral_countably_additive
-- name    : Rudin.ch11_integral_countably_additive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:19:07.858674+00:00
-- url     : https://prove2.me/theorems/4b12e57b-370a-4bf0-92f1-a46d91341a11
-- title:
--   Theorem 11.24 — the integral is a countably additive set function
-- statement:
--   If $f$ is integrable and $E_1, E_2, \dots$ are pairwise disjoint measurable sets with union $E$, then $\int_E f\,d\mu = \sum_n \int_{E_n} f\,d\mu$, the series being convergent.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 315, Theorem 11.24

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 11.24: the integral of an integrable function is a countably additive set
function. -/
theorem ch11_integral_countably_additive {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise (Function.onFun Disjoint E)) :
    HasSum (fun n => ∫ x in E n, f x ∂μ) (∫ x in ⋃ n, E n, f x ∂μ) := by sorry

end Rudin
