-- Prove2me | Theorems.Thm_SeqExpDiffusion_eq_16
-- name    : SeqExpDiffusion.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:52.063979+00:00
-- url     : https://prove2.me/theorems/7d67dc25-f538-4e2b-b62c-f7a783474537
-- title:
--   (16), p.19 — general solution of the continuation-region ODE
-- statement:
--   Let $r>0$, $\tilde\sigma>0$ and $\gamma=(1+\sqrt{1+8r/\tilde\sigma^2})/2$. Let $0\le a<b\le1$ and let $f$ be twice differentiable on $(a,b)$. Then $f$ solves
--
--   $$\frac{(\tilde\sigma\,\delta(1-\delta))^2}{2}\,f''(\delta)-r\,f(\delta)=0\qquad\text{for all }\delta\in(a,b)$$
--
--   if and only if there are constants $C^0,C^1$ with
--
--   $$f(\delta)=C^0\,\frac{(1-\delta)^\gamma}{\delta^{\gamma-1}}+C^1\,\frac{\delta^\gamma}{(1-\delta)^{\gamma-1}}\qquad\text{for all }\delta\in(a,b).$$
--
--   This identifies the value of a two-action problem in its continuation region up to two constants, which value matching and smooth pasting then fix.
--
--   Differences from the source:
--   - generalization: the value 𝒢̃_ij on the interior of its continuation region → any twice-differentiable f on any open interval (a, b) ⊆ (0, 1); reason: the continuation region is such an interval, so the statement specializes to the page
--   - reading: "whose general solution is given by" → both directions: every solution has the form, and every function of the form is a solution; reason: the meaning of "general solution"
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, display (16) and the ODE above it, p.19

import Definitions.Def_SeqExpDiffusion_gammaOf
import Definitions.Def_SeqExpDiffusion_contValue

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- The general solution (16), Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.19: in a continuation region the value solves
`(σ̃ δ (1 − δ))²/2 · 𝒢̃″_ij(δ) − r 𝒢̃_ij(δ) = 0`, whose general solution is
`𝒢̃_ij(δ) = C⁰ (1 − δ)^γ / δ^{γ−1} + C¹ δ^γ / (1 − δ)^{γ−1}`, `γ := (1 + √(1 + 8r/σ̃²))/2`, with
`C⁰`, `C¹` two constants of integration.

On any open interval `(a, b) ⊆ (0, 1)`, a twice differentiable `f` solves the ODE on `(a, b)` if and
only if it has this form there for some constants.

**Formalization Note** `contValue γ C₀ C₁ δ = C₀ (1 − δ)^γ δ^{1−γ} + C₁ (1 − δ)^{1−γ} δ^γ`, the same
function as printed in (16). "General solution" is read as both directions. -/
theorem eq_16 (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (f : ℝ → ℝ)
    (hf : ∀ δ ∈ Ioo a b, DifferentiableAt ℝ f δ ∧ DifferentiableAt ℝ (deriv f) δ) :
    (∀ δ ∈ Ioo a b, (σ * δ * (1 - δ)) ^ 2 / 2 * deriv (deriv f) δ - r * f δ = 0) ↔
      ∃ C₀ C₁ : ℝ, ∀ δ ∈ Ioo a b, f δ = contValue (gammaOf r σ) C₀ C₁ δ := by sorry

end SeqExpDiffusion
