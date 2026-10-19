-- Prove2me | Theorems.Thm_PoSShares_Stability_lemma_2
-- name    : PoSShares.Stability.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:37.199692+00:00
-- url     : https://prove2.me/theorems/06d7a09b-0a58-4e50-b33a-b6d4e8ea1837
-- title:
--   Lemma 2, (A11) — $\mathrm{Var}(\pi_{t+1}) = a_{t+1}\,\pi_0(1-\pi_0)$
-- statement:
--   In the PoS model, for every $t \ge 0$ the unconditional variance of the investor's share at $t+1$ is
--   $$\mathrm{Var}(\pi_{t+1}) = a_{t+1}\,\pi_0(1 - \pi_0), \qquad \pi_0 = \frac{n_0}{N_0},$$
--   where $a_1 = (R_1/N_1)^2$ and $a_{t+1} = a_t + (R_{t+1}/N_{t+1})^2(1 - a_t)$ is the sequence (A12).
--
--   It reduces every question about the spread of the shares to the deterministic sequence $a_t$.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 20, Lemma 2, (A11)–(A12)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Lemma 2, (A11)–(A12)**, p. 20. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

The unconditional variance of the investor's share at `t + 1` is
`Var(π_{t+1}) = a_{t+1} π_0 (1 − π_0)`, where `a_1 = (R_1/N_1)^2` and
`a_{t+1} = a_t + (R_{t+1}/N_{t+1})^2 (1 − a_t)` (`aSeq`).

**Formalization Note.** `π_0 = n_0 / N_0`. `Var` is Mathlib's `variance`; the shares are bounded,
so it is the true variance. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    variance (share M (t + 1)) μ =
      aSeq M.N₀ M.R (t + 1) * (M.n₀ / M.N₀ * (1 - M.n₀ / M.N₀)) := by sorry

end PoSShares.Stability
