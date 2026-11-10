-- Prove2me | Theorems.Thm_ThinShellSampling_eq_1_3
-- name    : ThinShellSampling.eq_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:06.232722+00:00
-- url     : https://prove2.me/theorems/60342000-804f-458f-b06f-d5bc435d5a3e
-- title:
--   Weak triangle inequality for Rényi divergence, (1.3)
-- statement:
--   Let $q>1$, $\lambda\in(0,1)$, and let $\mu,\nu,\pi$ be probability measures on a common measurable space. Then
--
--   $$
--   \mathsf R_q(\mu\,\|\,\pi)\le\frac{q-\lambda}{q-1}\,\mathsf R_{q/\lambda}(\mu\,\|\,\nu)+\mathsf R_{(q-\lambda)/(1-\lambda)}(\nu\,\|\,\pi).
--   $$
--
--   Rényi divergence is not a metric; this inequality is the substitute for the triangle inequality. In the annealing analysis it transfers warmness from one annealing target to the next (with $\lambda=1/2$, p.40).
--
--   **Formalization Note** Divergences take values in $[0,\infty]$, so the inequality holds trivially when a term on the right is infinite.
--
--   Differences from the source:
--
--   - encoding: R_q real-valued for μ ≪ ν → R_q in [0, ∞], equal to ∞ off absolute continuity; reason: Lean convention; the inequality is the same on every instance where all terms are finite and trivial otherwise
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.3, eq. (1.3), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Weak triangle inequality for Rényi divergence**, display (1.3).

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), §1.3, eq. (1.3), p.13 (PDF p.15): "for any `q > 1`, `λ ∈ (0, 1)`, and probability measures
`µ, ν, π`, it holds that `R_q(µ ‖ π) ≤ (q − λ)/(q − 1) R_{q/λ}(µ ‖ ν) + R_{(q−λ)/(1−λ)}(ν ‖ π)`."

**Formalization Note.** The divergences are `[0, ∞]`-valued (`renyi`), so the inequality also holds,
trivially, when a term on the right is infinite. The measures live on an arbitrary measurable space. -/
theorem eq_1_3 {α : Type*} [MeasurableSpace α] (q l : ℝ) (hq : 1 < q) (hl0 : 0 < l) (hl1 : l < 1)
    (μ ν π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] :
    renyi q μ π ≤
      ENNReal.ofReal ((q - l) / (q - 1)) * renyi (q / l) μ ν + renyi ((q - l) / (1 - l)) ν π := by sorry

end ThinShellSampling
