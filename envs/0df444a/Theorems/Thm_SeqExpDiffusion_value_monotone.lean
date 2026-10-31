-- Prove2me | Theorems.Thm_SeqExpDiffusion_value_monotone
-- name    : SeqExpDiffusion.value_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:19.577354+00:00
-- url     : https://prove2.me/theorems/f5cae78b-6053-43e9-a4ab-1155f9a5bd8c
-- title:
--   §4.3.3, p.21 — $\tilde{\mathcal G}\ge\tilde{\mathcal G}_{ij}$: a larger payoff has a larger value
-- statement:
--   Let $r>0$, $\tilde\sigma>0$, and let $H_1,H_2$ be payoffs continuous on $[0,1]$ with $H_1\le H_2$ on $[0,1]$. If $v_1$ and $v_2$ are the value functions of (12) with payoffs $H_1$ and $H_2$, then
--
--   $$v_1(\delta)\le v_2(\delta)\qquad\text{for all }\delta\in[0,1].$$
--
--   With $H_1=\tilde G_{ij}\le G=H_2$ this is the paper's "$\tilde{\mathcal G}(\delta)\ge\tilde{\mathcal G}_{ij}(\delta)$ for all $\delta\in[0,1]$", which gives $\tilde{\mathcal G}\ge\tilde V$.
--
--   Differences from the source:
--   - generalization: G̃_ij ≤ G, the payoffs of (1) and §4.3.2 → any payoffs H₁ ≤ H₂ continuous on [0, 1]; reason: G̃_ij and G are such payoffs, so the statement specializes to the page
--   - generalization: stopping times of the filtration 𝔽 of the experimentation history (p.8) → every probability space and every filtration for which the driving motion is Brownian; reason: the paper's setting is one instance, so the statement specializes to it
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, §4.3.3, p.21

import Definitions.Def_SeqExpDiffusion_IsValueFunction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, §4.3.3, p.21: "It follows that `𝒢̃(δ) ≥ 𝒢̃_ij(δ)` for all `δ ∈ [0, 1]`": the value of (12)
with payoff `G` dominates the value with payoff `G̃_ij ≤ G`.

Stated for any two payoffs continuous on `[0, 1]`: if `H₁ ≤ H₂` on `[0, 1]`, the value with payoff
`H₁` is at most the value with payoff `H₂` on `[0, 1]`.

**Formalization Note** The paper's `G` and `G̃_ij` are continuous on `[0, 1]` and `G̃_ij ≤ G`. -/
theorem value_monotone (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ) (H₁ H₂ v₁ v₂ : ℝ → ℝ)
    (hH₁ : ContinuousOn H₁ (Icc 0 1)) (hH₂ : ContinuousOn H₂ (Icc 0 1))
    (hle : ∀ δ ∈ Icc (0 : ℝ) 1, H₁ δ ≤ H₂ δ) (hv₁ : IsValueFunction r σ H₁ v₁)
    (hv₂ : IsValueFunction r σ H₂ v₂) :
    ∀ δ ∈ Icc (0 : ℝ) 1, v₁ δ ≤ v₂ δ := by sorry

end SeqExpDiffusion
