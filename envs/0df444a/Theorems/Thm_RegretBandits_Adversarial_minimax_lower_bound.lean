-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_minimax_lower_bound
-- name    : RegretBandits.Adversarial.minimax_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:07.483616+00:00
-- url     : https://prove2.me/theorems/fb3fa0db-b191-4e6b-9b9c-c6c37d32cae2
-- title:
--   Theorem 3.4 — minimax lower bound √(nK)/20
-- statement:
--   Let $n \ge K \ge 2$. For every forecaster there are Bernoulli means $\nu_1,\dots,\nu_K \in [0,1]$ such that, when the rewards $Y_{j,t} \in \{0,1\}$ of each arm $j$ are i.i.d. Bernoulli($\nu_j$) (independently across arms), every run of the forecaster satisfies
--   $$
--   \max_{j=1,\dots,K} \mathbb E\sum_{t=1}^n Y_{j,t} - \mathbb E\sum_{t=1}^n Y_{I_t,t} \ge \frac{1}{20}\sqrt{nK},
--   $$
--   with expectations over both the rewards and the forecaster's internal randomization. Since these instances belong to the class over which the book takes the supremum, this implies the book's
--   $$
--   \inf \sup \Bigl(\max_{i=1,\dots,K}\mathbb E\sum_{t=1}^n Y_{i,t} - \mathbb E\sum_{t=1}^n Y_{I_t,t}\Bigr) \ge \frac{1}{20}\sqrt{nK}. \qquad (3.18)
--   $$
--
--   The theorem shows that the $\sqrt{nK\ln K}$ upper bounds of Theorems 3.1–3.3 are optimal up to the logarithmic factor.
--
--   **Formalization Note** The book's standing assumption $n \ge K$ (protocol box, p. 6) is a hypothesis: without it the statement is false (for $n = 1$ and $K \ge 401$ the left side is at most $1 < \sqrt K/20$). The instance is chosen after the forecaster and before the run, as in "inf sup". The forecaster ranges over all rules mapping the observed past to a distribution on the arms (deterministic and randomized forecasters alike).
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 33, Theorem 3.4, Eq. (3.18)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_BernoulliModel

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Theorem 3.4 (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 33), minimax lower bound, in the form
"for every forecaster there is a hard instance". Let `n ≥ K ≥ 2`. For every forecaster `q` there
are Bernoulli means `ν ∈ [0,1]^K` such that every run of `q` on the instance where arm `j` gives
i.i.d. Bernoulli(`ν_j`) rewards satisfies
`max_j E ∑_{t=1}^n Y_{j,t} - E ∑_{t=1}^n Y_{I_t,t} ≥ √(nK)/20`. This implies (3.18). -/
theorem minimax_lower_bound {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : K ≤ n)
    (q : ℕ → (ℕ → Fin K) → (ℕ → Bool) → Fin K → ℝ) (hq : IsBanditForecaster q) :
    ∃ ν : Fin K → ℝ, (∀ j, ν j ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (I : ℕ → Ω → Fin K) (Y : ℕ → Ω → Fin K → Bool),
        IsBernoulliRun P ν q I Y →
          Real.sqrt (n * K) / 20 ≤
            (⨆ j : Fin K, ∫ ω, ∑ t ∈ Finset.Icc 1 n, rewardVal (Y t ω j) ∂P) -
              ∫ ω, ∑ t ∈ Finset.Icc 1 n, rewardVal (Y t ω (I t ω)) ∂P := by sorry

end RegretBandits.Adversarial
