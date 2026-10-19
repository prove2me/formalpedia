-- Prove2me | Theorems.Thm_PoSShares_Stability_variance_limit_eq
-- name    : PoSShares.Stability.variance_limit_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:35.154198+00:00
-- url     : https://prove2.me/theorems/dc758b76-d196-4916-8305-45ddda620dd1
-- title:
--   Proof of Proposition 4 (p. 24) — $\mathrm{Var}(\pi_\infty) = \lim_t a_t\,\pi_0(1-\pi_0)$
-- statement:
--   In the PoS model, let $\pi_\infty$ be a measurable almost-sure limit of the investor's share $\pi_t$. Then
--   $$a_t\,\pi_0(1 - \pi_0) \longrightarrow \mathrm{Var}(\pi_\infty) \qquad (t \to \infty),$$
--   where $a_t$ is the sequence (A12) and $\pi_0 = n_0/N_0$. In the paper's notation, $a_\infty = \mathrm{Var}(\pi_{1,\infty})/(\pi_1(1-\pi_1)) = \lim_{t\to\infty} a_t$.
--
--   It identifies the variance of the limiting share through the deterministic sequence $a_t$.
--
--   **Formalization Note.** Stated without dividing by $\pi_0(1-\pi_0)$.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 24, proof of Proposition 4 (a_∞ = lim_{t→∞} a_t)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Proof of Proposition 4**, p. 24: "Let a_∞ = Var(π_{1,∞})/(π_1(1−π_1)). The bounded
convergence then implies that a_∞ = lim_{t→∞} a_t." Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

For the almost-sure limit `π_∞` of the investor's share, `a_t π_0 (1 − π_0) → Var(π_∞)` as
`t → ∞`, i.e. `Var(π_∞) = lim_t Var(π_t)`.

**Formalization Note.** Stated without dividing by `π_0(1 − π_0)`, so it also covers
`π_0 ∈ {0, 1}`. `π_0 = n_0 / N_0`. -/
theorem variance_limit_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (hPoS : IsPoS μ M) (πinf : Ω → ℝ)
    (hmeas : Measurable πinf)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => share M t ω) atTop (𝓝 (πinf ω))) :
    Tendsto (fun t => aSeq M.N₀ M.R t * (M.n₀ / M.N₀ * (1 - M.n₀ / M.N₀))) atTop
      (𝓝 (variance πinf μ)) := by sorry

end PoSShares.Stability
