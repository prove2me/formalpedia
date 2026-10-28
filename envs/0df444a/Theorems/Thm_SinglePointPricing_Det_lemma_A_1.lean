-- Prove2me | Theorems.Thm_SinglePointPricing_Det_lemma_A_1
-- name    : SinglePointPricing.Det.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:59.60598+00:00
-- url     : https://prove2.me/theorems/7c4b6c83-8b57-4d1f-a85e-750dbaee5b88
-- title:
--   Lemma A-1, p. App-1 — the GPD tail Γ_α(β(v − s)) has constant α-virtual value (1 − α)s − 1/β
-- statement:
--   Fix $\alpha\in[0,1]$, $\beta>0$ and $s\ge0$, and consider the generalized Pareto tail $\overline F(v) = \Gamma_\alpha(\beta(v-s))$ for $v\ge s$, with density $f(v) = -\frac{d}{dv}\Gamma_\alpha(\beta(v-s))$. Its **α-virtual value** is constant:
--   $$\phi^\alpha_F(v) = (1-\alpha)v - \frac{\overline F(v)}{f(v)} = (1-\alpha)s - \frac1\beta\qquad\text{for all } v\ge s.$$
--
--   The generalized Pareto tails are therefore on the boundary of the α-strongly regular class; this is what makes every element of the worst-case family $\mathcal S_{\alpha,w,q}$ admissible.
--
--   Differences from the source:
--   - reading: 'The cumulative distribution function Γ_α(β(v − s))' → Γ_α(β(v − s)) is treated as a ccdf, with density f = −d/dv Γ_α(β(v − s)); reason: Γ_α decreases from 1, the α-virtual value is defined with F̄/f (App-1), and the proof differentiates it as a ccdf; 'cumulative distribution function' is a slip
--   - encoding: α implicit (Γ_α is defined for α ∈ [0, 1], p. 13) → hypothesis α ∈ [0, 1]; reason: the range on which Γ_α is defined
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Lemma A-1, p. App-1

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

namespace SinglePointPricing.Det

/-- Lemma A-1, p. App-1: for `β > 0` and `s ≥ 0`, the generalized Pareto tail `v ↦ Γ_α(β(v − s))`
on `v ≥ s` has constant `α`-virtual value `(1 − α)v − F̄(v)/f(v) = (1 − α)s − 1/β`, where the density
`f` is minus the derivative of the tail. -/
theorem lemma_A_1 (α β s : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : 0 < β) (hs : 0 ≤ s) :
    ∀ v : ℝ, s ≤ v →
      (1 - α) * v - GammaA α (β * (v - s)) / (-deriv (fun x => GammaA α (β * (x - s))) v)
        = (1 - α) * s - 1 / β := by sorry

end SinglePointPricing.Det
