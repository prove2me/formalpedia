-- Prove2me | Theorems.Thm_ThinShellSampling_corollary_5_3
-- name    : ThinShellSampling.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:19.328209+00:00
-- url     : https://prove2.me/theorems/8671ba80-c6ee-43bb-aa19-ddef47d5f6a4
-- title:
--   Corollary 5.3 — closeness of Gaussian tilts in the variance parameter
-- statement:
--   Let $\nu$ be a probability measure on $\mathbb R^n$, $\nu_s(dx)\propto e^{-s\|x\|^2}\nu(dx)$, $\mu_{\sigma^2}=\nu_{1/(2\sigma^2)}$, and $\mathcal V=\sup_{s\ge0}\operatorname{Var}_{\nu_s}(\|X\|^2)\in[0,\infty]$. For every $q>1$, $\sigma^2>0$ and $\alpha>0$,
--
--   $$
--   \mathsf R_q(\mu_{\sigma^2}\,\|\,\mu_{\sigma^2(1+\alpha)})\le\frac{q\mathcal V}{8\sigma^4}\Big(\frac{\alpha}{1+\alpha}\Big)^2\le\frac{q\mathcal V\alpha^2}{8\sigma^4}
--   \qquad\text{and}\qquad
--   \mathsf R_q(\mu_{\sigma^2}\,\|\,\nu)\le\frac{q\mathcal V}{8\sigma^4}.
--   $$
--
--   The first bound fixes the step size of the second annealing loop of Algorithm 6.6; the second shows that the terminal Gaussian tilt is a warm start for $\nu$ itself.
--
--   Differences from the source:
--
--   - reading: closing sentence "In particular, the update σ² ↦ σ²(1 + α) with α ≲ σ²/√(q𝒱) maintains O(1)-closeness, and σ² ≳ √(q𝒱) ensures terminal O(1)-warmness" → not stated; reason: it is an informal consequence of the displayed bounds, not a separate claim
--   - encoding: 𝒱 real → 𝒱 in [0, ∞] (supremum of evariance); reason: Lean convention; the bounds are trivial when 𝒱 = ∞
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Corollary 5.3, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_expTilt

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Corollary 5.3 (Closeness).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Corollary 5.3, p.31 (PDF p.33), with `ν_s(dx) ∝ e^{−s‖x‖²} ν(dx)` and
`µ_{σ²} := ν_{1/(2σ²)}` (p.31): "Let `V := sup_{s≥0} Var_{ν_s}(‖X‖²)`. For every `q > 1`, `σ² > 0`, and
`α > 0`, `R_q(µ_{σ²} ‖ µ_{σ²(1+α)}) ≤ qV/(8σ⁴) (α/(1 + α))² ≤ qVα²/(8σ⁴)` and
`R_q(µ_{σ²} ‖ ν) ≤ qV/(8σ⁴)`."

**Formalization Note.** `ν` is any probability measure on `ℝⁿ` (as in Lemma 5.2). `V ∈ [0, ∞]`
(`evariance`); all three inequalities are stated. The closing heuristic sentence of the corollary
("In particular, the update … maintains `O(1)`-closeness …") is not a separate claim. -/
theorem corollary_5_3 (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (q σ2 α : ℝ) (hq : 1 < q) (hσ : 0 < σ2) (hα : 0 < α) :
    let νs : ℝ → Measure (EuclideanSpace ℝ (Fin n)) := fun s => expTilt ν (fun x => s * ‖x‖ ^ 2)
    let μ : ℝ → Measure (EuclideanSpace ℝ (Fin n)) := fun τ => νs (1 / (2 * τ))
    let Vv : ℝ≥0∞ := ⨆ s : ℝ, ⨆ (_ : 0 ≤ s), evariance (fun x => ‖x‖ ^ 2) (νs s)
    renyi q (μ σ2) (μ (σ2 * (1 + α))) ≤
        ENNReal.ofReal (q / (8 * σ2 ^ 2) * (α / (1 + α)) ^ 2) * Vv ∧
      ENNReal.ofReal (q / (8 * σ2 ^ 2) * (α / (1 + α)) ^ 2) * Vv ≤
        ENNReal.ofReal (q * α ^ 2 / (8 * σ2 ^ 2)) * Vv ∧
      renyi q (μ σ2) ν ≤ ENNReal.ofReal (q / (8 * σ2 ^ 2)) * Vv := by sorry

end ThinShellSampling
