-- Prove2me | Theorems.Thm_RGGThreshold_lemma_4_1
-- name    : RGGThreshold.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:02:08.772557+00:00
-- url     : https://prove2.me/theorems/a4a01387-35e1-4869-b507-3a0aab58abe9
-- title:
--   Lemma 4.1 — log-concavity and second-order bound for $\Phi$
-- statement:
--   Let $\Phi$ be the standard Gaussian distribution function, $\phi$ its density and $\lambda(t)=\phi(t)/\Phi(t)$. For every $\alpha,\beta\in\mathbb R$,
--
--   $$
--   \Phi(\alpha+\beta)\le\Phi(\alpha)\exp\big(\lambda(\alpha)\beta\big),
--   $$
--
--   and
--
--   $$
--   \Phi(\alpha+\beta)\le\Phi(\alpha)\exp\Big(\lambda(\alpha)\beta-\lambda(\alpha)^2\frac{\beta^2}{2}-\alpha\lambda(\alpha)\frac{\beta^2}{2}+|\beta|^3\Big).
--   $$
--
--   The first inequality is the log-concavity of $\Phi$; the second is a second-order Taylor bound. They turn edge probabilities $\Phi(\pm z_p+\text{small})$ into exponentials in the vertex-exposure argument.
--
--   Differences from the source: none.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 4.1, eqs. (5)–(6), p.12 (PDF p.14)

import Mathlib
import Definitions.Def_RGGThreshold_gaussCDF

namespace RGGThreshold

/-- **Lemma 4.1** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric
Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 4.1, eqs. (5)–(6), p.12
(PDF p.14)). For every `α, β ∈ ℝ`, with `λ = ϕ/Φ`,
`Φ(α + β) ≤ Φ(α) exp(λ(α)β)` and
`Φ(α + β) ≤ Φ(α) exp(λ(α)β - λ(α)²β²/2 - αλ(α)β²/2 + |β|³)`. -/
theorem lemma_4_1 (α β : ℝ) :
    gaussCDF (α + β) ≤ gaussCDF α * Real.exp (millsLam α * β) ∧
    gaussCDF (α + β) ≤ gaussCDF α * Real.exp (millsLam α * β - millsLam α ^ 2 * β ^ 2 / 2 -
      α * millsLam α * β ^ 2 / 2 + |β| ^ 3) := by sorry

end RGGThreshold
