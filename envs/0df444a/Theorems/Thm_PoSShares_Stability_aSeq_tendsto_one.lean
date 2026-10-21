-- Prove2me | Theorems.Thm_PoSShares_Stability_aSeq_tendsto_one
-- name    : PoSShares.Stability.aSeq_tendsto_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:28.224794+00:00
-- url     : https://prove2.me/theorems/ee5a8283-4fe7-413c-96c5-5aaf3795ed5f
-- title:
--   Proof of Proposition 4 (p. 24) — for $\gamma \ge 1$, $a_t \to 1$
-- statement:
--   Let $\rho > 0$, $\gamma \ge 1$ and $N > 0$. For all $t \ge 1$ let $R_t = \rho N_{t-1}^{\gamma}$ and $N_t = N + \sum_{n=1}^t R_n$, and let $a_t$ be the sequence (A12). Then
--   $$\lim_{t \to \infty} a_t = 1.$$
--
--   Combined with the previous milestone, the limiting share has the largest possible variance $\pi_1(1-\pi_1)$ for every initial supply $N$.
--
--   **Formalization Note.** The page writes "$\lim_{N\to\infty} a_t = 1$"; the conclusion it draws ("$a_\infty = 1$") needs, and the argument gives, the limit $t \to \infty$ for each fixed $N > 0$. That corrected reading is stated.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 24, proof of Proposition 4 (a_∞ = 1 for γ ≥ 1)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Proof of Proposition 4**, p. 24: for `γ ≥ 1`, `a_∞ = 1`. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

Let `ρ > 0`, `γ ≥ 1` and `N > 0`, with `R_t = ρ N_{t−1}^γ` for `t ≥ 1` and
`N_t = N + Σ_{n=1}^t R_n`. Then the sequence `a_t` of (A12) converges to `1` as `t → ∞`.

**Formalization Note.** The page writes "lim_{N→∞} a_t = 1"; what the conclusion "a_∞ = 1" needs,
and what holds, is `a_t → 1` as `t → ∞` for each fixed `N > 0` (the ratio `R_{t+1}/N_{t+1}` is
bounded below by `ρN^{γ−1}/(1 + ρN^{γ−1}) > 0` because `N_t ≥ N`). This corrected reading is
stated. Powers are real powers. -/
theorem aSeq_tendsto_one (ρ γ N : ℝ) (R : ℕ → ℝ) (hρ : 0 < ρ) (hγ : 1 ≤ γ) (hN : 0 < N)
    (hR : IsPowerReward ρ γ N R) :
    Tendsto (aSeq N R) atTop (𝓝 1) := by sorry

end PoSShares.Stability
