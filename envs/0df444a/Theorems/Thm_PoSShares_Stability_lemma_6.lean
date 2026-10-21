-- Prove2me | Theorems.Thm_PoSShares_Stability_lemma_6
-- name    : PoSShares.Stability.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:42.847111+00:00
-- url     : https://prove2.me/theorems/e0ce2d53-ddbd-43df-b2c6-faa22e5175d2
-- title:
--   Lemma 6 — $\lim_N \mathrm{Var}(\pi_{1,\infty}) = 0$ implies $\lim_N \mathbb{P}(|\pi_{1,\infty}-\pi_1| \ge \varepsilon) = 0$
-- statement:
--   Consider PoS models indexed by the initial number of coins $N \in \mathbb{N}$, all on one probability space, where model $N \ge 1$ has initial supply $N_0 = N$ and investor 1 starts with the fixed share $\pi_1$ (endowment $n_0 = \pi_1 N$). Let $\pi_{1,\infty}$ (depending on $N$) be a measurable almost-sure limit of her share. The rewards are arbitrary. If
--   $$\lim_{N \to \infty} \mathrm{Var}(\pi_{1,\infty}) = 0, \qquad \text{(A27)}$$
--   then for every $\varepsilon > 0$,
--   $$\lim_{N \to \infty} \mathbb{P}\big(|\pi_{1,\infty} - \pi_1| \ge \varepsilon\big) = 0. \qquad \text{(A28)}$$
--
--   This is the Chebyshev step that turns a vanishing variance into concentration of the limiting share at the initial share.
--
--   **Formalization Note.** The model with index $0$ is constrained only by $n_0 = \pi_1 N_0$. The limit $\pi_{1,\infty}$ is bounded, so its variance is the true variance.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 23, Lemma 6, (A27)–(A28)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Lemma 6, (A27)–(A28)**, p. 23. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

Consider the family of models indexed by the initial number of coins `N`, with the tracked
investor's initial share fixed at `π_1` (endowment `π_1 N`), and let `π_{1,∞}` be the
almost-sure limit of her share (Proposition 1). The condition `lim_{N→∞} Var(π_{1,∞}) = 0` implies
that for any `ε > 0`, `lim_{N→∞} P(|π_{1,∞} − π_1| ≥ ε) = 0`.

**Formalization Note.** All models of the family live on one probability space; the model with
index `N ≥ 1` has `N_0 = N` (the index-0 model is constrained only by `n_0 = π_1 N_0`). The
endowment `π_1 N` is real. The limit `π_{1,∞}` is any measurable almost-sure limit of the shares;
it is bounded, so its variance is the true variance. Rewards are arbitrary (Lemma 6 does not use the
reward rule). -/
theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π₁ : ℝ) (M : ℕ → Model Ω) (hPoS : ∀ N, IsPoS μ (M N))
    (hN : ∀ N : ℕ, 1 ≤ N → (M N).N₀ = N) (hn : ∀ N, (M N).n₀ = π₁ * (M N).N₀)
    (πinf : ℕ → Ω → ℝ) (hmeas : ∀ N, Measurable (πinf N))
    (hlim : ∀ N, ∀ᵐ ω ∂μ, Tendsto (fun t => share (M N) t ω) atTop (𝓝 (πinf N ω)))
    (hvar : Tendsto (fun N => variance (πinf N) μ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => μ.real {ω | ε ≤ |πinf N ω - π₁|}) atTop (𝓝 0) := by sorry

end PoSShares.Stability
