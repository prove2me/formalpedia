-- Prove2me | Theorems.Thm_OutlierAssort_ActiveElim_regret_sum_bound
-- name    : OutlierAssort.ActiveElim.regret_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:21.529236+00:00
-- url     : https://prove2.me/theorems/10cede31-86c6-4287-aeb4-70a673909b6e
-- title:
--   (8)–(11), proof of Theorem 1, pp. 14–15 (corrected: false middle step of (8) dropped) — Σ_{τ≤τ₀} 4∆̂_ε̄(τ)T_τ ≲ ε̄K²T log T + (K²√ε̄ + √K)√(NT log³T) + K²N log²T
-- statement:
--   Fix the epoch schedule of Algorithm 1:
--
--   - $T_0 = \lceil 128(K+1)^2N\ln T\rceil$ and $T_\tau = 2^\tau T_0$;
--   - $\tau_0$ is the epoch that contains the last period $T-1$.
--
--   Let $N_\sigma \le N$ be any active-set sizes. Let $\hat\Delta_{\bar\varepsilon}(0) = 1$, and let $\hat\Delta_{\bar\varepsilon}(\sigma+1)$ be the error bound of line 15 of Algorithm 1 for an epoch of length $T_\sigma$ with $N_\sigma$ active items:
--   $$
--   \hat\Delta_{\bar\varepsilon}(\sigma+1) = \begin{cases} 1, & T_\sigma < \frac{\bar\varepsilon T}{4(K+1)},\\[2pt] 16K(K+1)\Big(\frac{\bar\varepsilon_\sigma}{2} + \sqrt{\frac{\bar\varepsilon_\sigma N_\sigma \ln T}{T_\sigma}} + \frac{2N_\sigma\ln T}{3T_\sigma}\Big) + 16\sqrt{\frac{K N_\sigma \ln T}{T_\sigma}}, & \text{otherwise,}\end{cases}
--   $$
--   with $\bar\varepsilon_\sigma = \min\{1,\bar\varepsilon T/T_\sigma\}$. There are universal constants $C$ and $T_1$ such that for all $T \ge T_1$, $1 \le N \le T$, $K \ge 1$ and $\bar\varepsilon \ge 0$,
--   $$
--   \sum_{\tau=0}^{\tau_0} 4\hat\Delta_{\bar\varepsilon}(\tau)\,T_\tau \le C\Big(\bar\varepsilon K^2 T\log T + \big(K^2\sqrt{\bar\varepsilon} + \sqrt K\big)\sqrt{NT\log^3 T} + K^2N\log^2T\Big).
--   $$
--
--   This is the summation that turns the per-period regret bound of Lemma 4 into the regret bound of Theorem 1. Epochs before $\tau^*$, the first with $T_{\tau^*} \ge \bar\varepsilon T/4(K+1)$, are covered by (8); the remaining epochs are summed by (9)–(11).
--
--   Differences from the source:
--   - correction: (8) $\sum_{\tau<\tau^*} T_\tau \le T_{\tau^*} \le \bar\varepsilon T$ → only the outer bound enters, through $\hat\Delta_{\bar\varepsilon}(\tau) = 1$ for $\tau \le \tau^*$; reason: the middle step fails when $\tau^* = 0$ (e.g. $\bar\varepsilon = 0$: $T_{\tau^*} = T_0 > 0 = \bar\varepsilon T$), while the outer bound is what the proof uses.
--   - reading: the chain (8)–(11) for the active-set sizes of a run → one inequality for every sequence $N_\sigma \le N$; reason: the chain uses only $|\mathcal A^{(\tau+1)}| \le N$.
--   - reading: "$\lesssim$" → $\exists\, C, T_1$ placed before all other quantifiers; reason: "universal constant" and "for sufficiently large $T$" of Theorem 1.
--   - encoding: the display (9) pairs $T_\tau$ with $|\mathcal A^{(\tau+1)}|$ inside $\hat\Delta(\tau)$ → $\hat\Delta(\sigma+1)$ uses $T_\sigma$ and $N_\sigma$, as line 15 defines it; reason: the indices of Algorithm 1, a factor 2 absorbed by $C$.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, pp. 14–15, proof of Theorem 1, (8)–(11)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm

namespace OutlierAssort.ActiveElim

/-- (8)–(11), proof of Theorem 1 (pp. 14–15): the sum `∑_{τ=0}^{τ₀} 4 ∆̂_ε̄(τ) T_τ` over the epoch
schedule, with `∆̂_ε̄(0) = 1` and `∆̂_ε̄(σ + 1)` given by line 15 for `T_σ` and any active-set sizes
`N_σ ≤ N`, is at most `C (ε̄ K² T log T + (K² √ε̄ + √K) √(N T log³ T) + K² N log² T)` for universal
`C` and all `T ≥ T₁`. -/
theorem regret_sum_bound :
    ∃ C T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → N ≤ T → 1 ≤ K →
      ∀ (epsBar : ℝ), 0 ≤ epsBar →
      ∀ (n : ℕ → ℕ), (∀ σ, n σ ≤ N) →
        4 * 1 * (epochLen N K T 0 : ℝ) +
            ∑ σ ∈ Finset.range (tau0 N K T),
              4 * deltaHat epsBar T K (epochLen N K T σ) (n σ) * (epochLen N K T (σ + 1) : ℝ) ≤
          C * (epsBar * K ^ 2 * T * Real.log T +
            (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * Real.log T ^ 3) +
            K ^ 2 * N * Real.log T ^ 2) := by sorry

end OutlierAssort.ActiveElim
