-- Prove2me | Theorems.Thm_PoSShares_Stability_proposition_1
-- name    : PoSShares.Stability.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:53.613764+00:00
-- url     : https://prove2.me/theorems/96165879-2972-462a-b406-30ec1f4e6abf
-- title:
--   Proposition 1 — the share is a martingale with an a.s. limit $\pi_\infty$ of mean $\pi_0$
-- statement:
--   Suppose the investor never trades any coins, and the PoS protocol selects her before date $t+1$ with probability $\pi_t$. Then:
--   1. her share $(\pi_t)_{t \ge 0}$ is a martingale with respect to the filtration $(\mathcal{F}_t)$;
--   2. there is a measurable random variable $\pi_\infty$ such that $\pi_t \to \pi_\infty$ almost surely, $\pi_\infty \in [0, 1]$ almost surely, and
--   $$\mathbb{E}(\pi_\infty) = \pi_0 = \frac{n_0}{N_0}.$$
--
--   The PoS protocol therefore does not make the rich richer on average: the expected long-run share equals the initial share.
--
--   **Formalization Note.** The paper's "well-defined limiting distribution" is read as the almost-sure limit its proof constructs from the martingale convergence theorem (p. 18). The selection rule is encoded as $\mathbb{E}[\mathbf{1}_{S_{t+1}} \mid \mathcal{F}_t] = \pi_t$.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 8, Proposition 1 (proof pp. 17–18)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Proposition 1**, p. 8 (proof pp. 17–18). Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

Suppose the investor never trades any coins. Then her share `π_t` is a martingale with respect to
the PoS filtration. Moreover it has a limit `π_∞` almost surely, `π_∞ ∈ [0, 1]` almost surely, and
`E(π_∞) = π_0 = n_0 / N_0`.

**Formalization Note.** "Never trades" is built into the model through (5). The selection rule is
the conditional-expectation condition `IsPoS` (the page's independence assumption cannot be
literal; see the model file). The page's "well-defined limiting distribution" is read as the
almost-sure limit the proof constructs ("the martingale convergence theorem implies that π_{i,t}
has a well-defined limit", p. 18); the limit is taken measurable. The conjunct `π_∞ ∈ [0, 1]` a.s.
is immediate from `0 ≤ π_t ≤ 1` and is used in (A30). -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model Ω) (hPoS : IsPoS μ M) :
    Martingale (share M) M.ℱ μ ∧
      ∃ πinf : Ω → ℝ, Measurable πinf ∧
        (∀ᵐ ω ∂μ, Tendsto (fun t => share M t ω) atTop (𝓝 (πinf ω))) ∧
        (∀ᵐ ω ∂μ, πinf ω ∈ Set.Icc (0 : ℝ) 1) ∧
        ∫ ω, πinf ω ∂μ = M.n₀ / M.N₀ := by sorry

end PoSShares.Stability
