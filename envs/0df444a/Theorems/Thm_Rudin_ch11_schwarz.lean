-- Prove2me | Theorems.Thm_Rudin_ch11_schwarz
-- name    : Rudin.ch11_schwarz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:38:26.178975+00:00
-- url     : https://prove2.me/theorems/fe355e83-e7fb-4968-8222-6911dfb2cf08
-- title:
--   Theorem 11.35 — the Schwarz inequality in $\mathscr{L}^2$
-- statement:
--   If $f, g \in \mathscr{L}^2(\mu)$ then $fg$ is integrable and $\left|\int fg\,d\mu\right| \le \|f\|_2\,\|g\|_2$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 326, Theorem 11.35

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 11.35 (Schwarz inequality in `ℒ²`): if `f, g ∈ ℒ²(μ)` then `f g` is
integrable and `|∫ f g dμ| ≤ ‖f‖₂ ‖g‖₂`. -/
theorem ch11_schwarz {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : MemL2 μ f) (hg : MemL2 μ g) :
    Integrable (fun x => f x * g x) μ ∧
      |∫ x, f x * g x ∂μ| ≤ L2Norm μ f * L2Norm μ g := by sorry

end Rudin
