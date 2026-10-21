-- Prove2me | Theorems.Thm_PoSShares_Stability_lemma_1
-- name    : PoSShares.Stability.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:50.886678+00:00
-- url     : https://prove2.me/theorems/87eb0a25-6cd5-48f4-a800-36cb9bf4ebc1
-- title:
--   Lemma 1, (A8) — $\mathrm{Var}_t(\pi_{t+1}) = (R_{t+1}/N_{t+1})^2\,\pi_t(1-\pi_t)$
-- statement:
--   In the PoS model, the conditional variance at $t$ of the investor's share at $t+1$ is
--   $$\mathrm{Var}_t(\pi_{t+1}) = \Big(\frac{R_{t+1}}{N_{t+1}}\Big)^2 \pi_t(1 - \pi_t)$$
--   almost surely, for every $t \ge 0$. Here $\mathrm{Var}_t(X) = \mathbb{E}\big[(X - \mathbb{E}[X \mid \mathcal{F}_t])^2 \mid \mathcal{F}_t\big]$.
--
--   This feeds the recursion for the unconditional variance (Lemma 2).
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 19, Lemma 1, (A8)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Lemma 1, (A8)**, p. 19. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

The conditional variance at `t` of the investor's share at `t + 1` is
`Var_t(π_{t+1}) = (R_{t+1}/N_{t+1})^2 π_t (1 − π_t)`.

**Formalization Note.** `Var_t` is Mathlib's `condVar (ℱ t)`, i.e. `E[(X − E[X | ℱ_t])^2 | ℱ_t]`,
and the identity holds almost surely. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    condVar (M.ℱ t) (share M (t + 1)) μ =ᵐ[μ]
      fun ω => (M.R (t + 1) / coinSupply M.N₀ M.R (t + 1)) ^ 2 *
        (share M t ω * (1 - share M t ω)) := by sorry

end PoSShares.Stability
