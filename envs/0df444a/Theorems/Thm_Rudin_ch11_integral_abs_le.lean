-- Prove2me | Theorems.Thm_Rudin_ch11_integral_abs_le
-- name    : Rudin.ch11_integral_abs_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:21:06.819427+00:00
-- url     : https://prove2.me/theorems/3cd13040-b672-43fa-8b5e-fbc621dea9d4
-- title:
--   Theorems 11.26 and 11.27 — comparison and the triangle inequality
-- statement:
--   If $f$ is integrable then $|f|$ is integrable and $\left|\int f\,d\mu\right| \le \int |f|\,d\mu$; and if $f$ is measurable, $g$ is integrable and $|f| \le g$, then $f$ is integrable.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, pp. 317-318, Theorems 11.26 and 11.27

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorems 11.26 and 11.27: if `f` is integrable then so is `|f|` and
`|∫ f| ≤ ∫ |f|`; and a measurable function dominated by an integrable function is
integrable. -/
theorem ch11_integral_abs_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ) :
    (Integrable f μ → Integrable (fun x => |f x|) μ ∧ |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ) ∧
    (Measurable f → Integrable g μ → (∀ x, |f x| ≤ g x) → Integrable f μ) := by sorry

end Rudin
