-- Prove2me | Theorems.Thm_RiskUncSets_Distortion_lemma_4_1
-- name    : RiskUncSets.Distortion.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:50.236431+00:00
-- url     : https://prove2.me/theorems/580cd4e8-9bda-48d3-8d9d-c25f7a67f536
-- title:
--   Lemma 4.1, p. 1488 — under the uniform ℙ, a risk measure is a distortion risk measure iff it is a mixture ∫ CVaR_α(X) ν(dα)
-- statement:
--   Let $\Omega = \{\omega_1, \dots, \omega_N\}$, $N \ge 1$, carry the uniform distribution $\mathbb P\{\omega_i\} = 1/N$ (Assumption 4.1), and let $\mu : \mathbb R^N \to \mathbb R$ be a risk measure. Then $\mu$ is a distortion risk measure if and only if there is a probability measure $\nu$ on $(0, 1]$ such that
--   $$\mu(X) = \int_{(0,1]} \mathrm{CVaR}_\alpha(X)\,\nu(d\alpha) \qquad \text{for all } X \in \mathbb R^N.$$
--
--   Distortion risk measures are thus exactly the mixtures of conditional values-at-risk. On a finite uniform space this is the discrete counterpart of Kusuoka's representation for atomless spaces.
--
--   **Formalization Note** The page writes $\nu$ as "a function $\nu : [0,1] \to [0,1]$ satisfying $\int_{\alpha = 0}^1 \nu(d\alpha) = 1$" and integrates from $\alpha = 0$, where $\mathrm{CVaR}_\alpha$ (defined for $\alpha \in (0,1]$) is undefined. The statement reads $\nu$ as a probability measure on $\mathbb R$ with $\nu((0,1]^c) = 0$ and integrates over $(0,1]$. Nothing is lost: under the uniform distribution $\mathrm{CVaR}_\alpha = \mathrm{CVaR}_{1/N}$ for $\alpha \le 1/N$, so an atom at $0$ can be moved to $1/N$. For fixed $X$, $\alpha \mapsto \mathrm{CVaR}_\alpha(X)$ is monotone on $(0,1]$ and lies between $\mathbb E[-X]$ and $-\min_i X_i$, hence is $\nu$-integrable; the Bochner integral is therefore the genuine one. CVaR is taken under the uniform vector `uniform N`.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1488, Lemma 4.1; CVaR, p. 1485; Assumption 4.1, p. 1488

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

namespace RiskUncSets.Distortion

open MeasureTheory

theorem lemma_4_1 {N : ℕ} (hN : 0 < N) (μ : (Fin N → ℝ) → ℝ) (hμ : IsRiskMeasure μ) :
    IsDistortion (uniform N) μ ↔
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Set.Ioc (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ X : Fin N → ℝ, μ X = ∫ α in Set.Ioc (0 : ℝ) 1, cvar (uniform N) α X ∂ν := by sorry

end RiskUncSets.Distortion
