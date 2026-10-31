-- Prove2me | Theorems.Thm_SeqExpDiffusion_proposition_5_constants
-- name    : SeqExpDiffusion.proposition_5_constants
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:08.864334+00:00
-- url     : https://prove2.me/theorems/4220741c-0f43-41dc-bf40-477663ce4e21
-- title:
--   Proof of Proposition 5, p.51 — the constants $C^0_{ij}(\underline\delta)$, $C^1_{ij}(\underline\delta)$
-- statement:
--   Let $r>0$, $\tilde\sigma>0$, $\gamma=(1+\sqrt{1+8r/\tilde\sigma^2})/2$, let $\tilde R(\delta)=\tilde\alpha+\tilde\beta\delta$ be an affine payoff, $\underline\delta\in(0,1)$, and $u(\delta)=C^0(1-\delta)^\gamma\delta^{1-\gamma}+C^1(1-\delta)^{1-\gamma}\delta^\gamma$. Value matching $u(\underline\delta)=\tilde R(\underline\delta)$ and smooth pasting $u'(\underline\delta)=\tilde\beta$ hold if and only if
--
--   $$C^0=\left[\frac{(\gamma-1)\,\underline\delta\,\tilde\beta+(\gamma-\underline\delta)\,\tilde\alpha}{(2\gamma-1)\,\underline\delta}\right]\left(\frac{\underline\delta}{1-\underline\delta}\right)^{\gamma},\qquad C^1=\left[\frac{\gamma\,\underline\delta\,\tilde\beta+(\gamma-1+\underline\delta)\,\tilde\alpha}{(2\gamma-1)\,\underline\delta}\right]\left(\frac{1-\underline\delta}{\underline\delta}\right)^{\gamma-1}.$$
--
--   These are the constants of the auxiliary function $V(\delta;\underline\delta)$ through which the paper proves the existence of the thresholds in Proposition 5.
--
--   Differences from the source:
--   - reading: "the constants … are equal to" → an equivalence: the displayed pair satisfies value matching and smooth pasting at δ̲, and is the only pair that does; reason: the stronger of the two readings, and the one the proof uses
--   - encoding: δ̲ ∈ [0, δ̂_ij] → δ̲ ∈ (0, 1) excludes δ̲ = 0; reason: the formulas divide by δ̲, so they are undefined at δ̲ = 0
--   - generalization: δ̲ ≤ δ̂_ij and the payoff R̃_i of the left action → any δ̲ < 1 and any affine payoff α̃ + β̃δ; reason: the identity is algebraic and holds for every such δ̲, so it specializes to the page
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, proof of Proposition 5, p.51

import Definitions.Def_SeqExpDiffusion_gammaOf
import Definitions.Def_SeqExpDiffusion_contValue

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- The constants of integration as functions of the lower threshold, proof of Proposition 5,
Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.51: for a payoff `R̃_i(δ) = α̃_i + β̃_i δ` and `δ̲ ∈ (0, 1)`, value matching and smooth pasting
at `δ̲` hold exactly for
`C⁰_ij(δ̲) = [((γ − 1) δ̲ β̃_i + (γ − δ̲) α̃_i)/((2γ − 1) δ̲)] (δ̲/(1 − δ̲))^γ` and
`C¹_ij(δ̲) = [(γ δ̲ β̃_i + (γ − 1 + δ̲) α̃_i)/((2γ − 1) δ̲)] ((1 − δ̲)/δ̲)^{γ−1}`.

**Formalization Note** "are equal to" is stated as an equivalence: the displayed pair matches, and it
is the only pair that does. `γ = gammaOf r σ`. -/
theorem proposition_5_constants (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ) (αt βt d : ℝ)
    (hd : d ∈ Ioo (0 : ℝ) 1) (C₀ C₁ : ℝ) :
    (contValue (gammaOf r σ) C₀ C₁ d = αt + βt * d ∧
        HasDerivAt (contValue (gammaOf r σ) C₀ C₁) βt d) ↔
      (C₀ = ((gammaOf r σ - 1) * d * βt + (gammaOf r σ - d) * αt) /
            ((2 * gammaOf r σ - 1) * d) * (d / (1 - d)) ^ gammaOf r σ ∧
        C₁ = (gammaOf r σ * d * βt + (gammaOf r σ - 1 + d) * αt) /
            ((2 * gammaOf r σ - 1) * d) * ((1 - d) / d) ^ (gammaOf r σ - 1)) := by sorry

end SeqExpDiffusion
