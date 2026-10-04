-- Prove2me | Theorems.Thm_RegretBandits_Contextual_exp3_sampled_pseudo_regret
-- name    : RegretBandits.Contextual.exp3_sampled_pseudo_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:51:27.736493+00:00
-- url     : https://prove2.me/theorems/adf0d240-0512-4031-8587-987d515994e5
-- title:
--   Theorem 4.3 — Exp3 analysis when arms are drawn from other distributions (corrected rate)
-- statement:
--   Consider a $K$-armed bandit game, $K \ge 2$, with losses $\ell_{i,t} \in [0,1]$ assigned by an adaptive adversary, in which the arm $I_t$ played at round $t$ is drawn from a distribution $q_t$ over arms that may depend arbitrarily on the past, with $q_{i,t} \ge \varepsilon > 0$ for all $i$ and $t$. Run Exp3 without mixing with the estimates $\widetilde\ell_{i,t} = \frac{\ell_{i,t}}{q_{i,t}}\mathbb 1_{I_t=i}$ and the learning rate
--   $$\eta = \sqrt{\frac{2\varepsilon\ln K}{n}},$$
--   and let $p_t$ be its distribution at round $t$. Then for every arm $k$,
--   $$\mathbb E_{I^n\sim q^n}\left[\sum_{t=1}^n \mathbb E_{i\sim p_t}\ell_{i,t} - \sum_{t=1}^n \ell_{k,t}\right] \le \sqrt{\frac{2n}{\varepsilon}\ln K},$$
--   where $I^n \sim q^n$ means that each $I_t$ is drawn from $q_t$.
--
--   The result lets an Exp3 instance serve as an expert inside another forecaster that decides which arms are actually played, as in the Exp4-over-S-Exp3 construction of Section 4.2.1.
--
--   **Formalization Note** Corrected misprint: the book prints $\eta = \sqrt{2\ln K/(nK)}$. Its proof (p. 51) bounds the left side by $\frac{\eta n}{2\varepsilon} + \frac{\ln K}{\eta}$, which equals $\sqrt{(2n/\varepsilon)\ln K}$ exactly for $\eta = \sqrt{2\varepsilon\ln K/n}$; with the printed rate it gives a larger value unless $\varepsilon = 1/K$. The Lean statement uses the rate for which the proof yields (4.7). The book lets $q_t$ depend on the pairs $(I_s, \ell_{I_s,s})$, $s < t$; since the adversary's losses are functions of the past plays, a rule depending on the past plays covers this. The maximum over $k$ is written as "for every $k$".
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 50, Theorem 4.3, Eq. (4.7); proof p. 50-51

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol
import Definitions.Def_RegretBandits_Contextual_Exp3Sampled

namespace RegretBandits.Contextual

/-- Theorem 4.3, with the learning rate corrected (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2,
p. 50; the book prints `η = √(2 ln K/(nK))`, but its proof on p. 51 gives `ηn/(2ε) + ln K/η`,
which equals the bound (4.7) for `η = √(2 ε ln K / n)`). If the played arms are drawn from
arbitrary history-dependent distributions `q_t` with `q_{i,t} ≥ ε > 0`, and Exp3 without mixing is
run with `ℓ̃_{i,t} = ℓ_{i,t}/q_{i,t} 1{I_t = i}` and `η = √(2 ε ln K / n)`, then against any
adaptive adversary with losses in `[0,1]`, for every arm `k`,
`E_{I^n∼q^n}[∑_t E_{i∼p_t} ℓ_{i,t} - ∑_t ℓ_{k,t}] ≤ √((2n/ε) ln K)`. -/
theorem exp3_sampled_pseudo_regret {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : PlayRule K) (hq : ∀ t h, IsProbVec (q t h)) (hqε : ∀ t h i, ε ≤ q t h i)
    (ℓ : AdaptiveLosses K) (hℓ : ∀ t h i, 0 ≤ ℓ t h i ∧ ℓ t h i ≤ 1) (k : Fin K) :
    pathExpect q n
        (fun ω => ∑ t : Fin n,
          (∑ i, exp3SampledDist (Real.sqrt (2 * ε * Real.log K / n)) q ℓ t (playPrefix ω t) i *
              ℓ t (playPrefix ω t) i -
            ℓ t (playPrefix ω t) k)) ≤
      Real.sqrt (2 * n / ε * Real.log K) := by sorry

end RegretBandits.Contextual
