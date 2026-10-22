-- Prove2me | Theorems.Thm_PerishShip_Waste_avg_optimal_of_pathwise_regret
-- name    : PerishShip.Waste.avg_optimal_of_pathwise_regret
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T21:12:28.793001+00:00
-- url     : https://prove2.me/theorems/b022108b-2df7-4822-a33e-6a602f8a6618
-- title:
--   Bounded sample-path regret implies long-run average optimality (block argument)
-- statement:
--   Consider a controlled Markov process on a countable state space $S$ with actions in $A$, driven by i.i.d. shocks $\omega_0,\omega_1,\dots$ with law $\mu$ on a countable set $\Omega$: from state $s$ under action $a$ and shock $\omega$ the next state is $\mathrm{step}(s,a,\omega)$ and the period cost is $c(s,a,\omega)\in[0,\infty]$. For a (time-dependent, deterministic) Markov policy $\pi$ and initial state $s_0$ write $\overline J^{+}(\pi;s_0)$ and $\overline J^{-}(\pi;s_0)$ for the upper and lower limits of the Cesàro averages $\frac1T\sum_{t<T}\mathbb E_{s_0}^{\pi}[c(X_t,\pi_t(X_t),\omega_t)]$.
--
--   Let $f$ be a stationary decision rule, $\sigma$ a Markov policy, $s_0\in S$ and $F\subseteq S$. Assume
--
--   1. $s_0\in F$ and $F$ is closed under $f$: $\mathrm{step}(s,f(s),\omega)\in F$ for all $s\in F$ and all shocks $\omega$;
--   2. the costs of $f$ on $F$ are bounded by a finite constant $B$;
--   3. (bounded sample-path regret) there is a finite constant $C$ such that for every shock sequence $(\omega_t)$, every starting state $x\in F$ and every horizon $T$, the cost accumulated by $f$ started at $x$ along that shock sequence is at most the cost accumulated by $\sigma$ started at $s_0$ along the same shock sequence, plus $C$:
--   $$\sum_{t<T} c(u_t,f(u_t),\omega_t)\ \le\ \sum_{t<T} c(v_t,\sigma_t(v_t),\omega_t)+C,$$
--   where $u_0=x$, $u_{t+1}=\mathrm{step}(u_t,f(u_t),\omega_t)$ and $v_0=s_0$, $v_{t+1}=\mathrm{step}(v_t,\sigma_t(v_t),\omega_t)$.
--
--   Then
--   $$\overline J^{+}(f;s_0)\ \le\ \overline J^{-}(\sigma;s_0).$$
--
--   The point of the hypothesis is that $f$ may be compared with $\sigma$ from a *different* starting state: this is what converts a sample-path comparison with an additive constant into a comparison of an upper limit with a lower limit, which fails for comparisons from the same initial state only. The lemma is the probabilistic half of the proof that shipping oldest first in full minimizes the long-run average warehouse waste (Theorem 1 of Akkaş–Honhon); the combinatorial half is the sample-path regret bound for that policy.
--
--   **Formalization Note** The process law, expected period cost and Cesàro limits are those of `Def_PerishShip_Waste_AverageMDP` (`controlledStateLaw`, `controlledAvgUpper`, `controlledAvgLower`), valued in `ℝ≥0∞`. Sample paths are given as arbitrary functions satisfying the recursions.
-- source:
--   Auxiliary lemma for the proof of Akkaş & Honhon, Shipment policies for products with fixed shelf lives: impact on profits and waste, SSRN 3247290 (manuscript of 2021-03-20), p. 15 (PDF 15), Theorem 1 (first sentence); standard block/renewal argument for long-run average costs

import Mathlib
import Definitions.Def_PerishShip_Waste_AverageMDP

namespace PerishShip.Waste

/-- Average optimality from a bounded sample-path regret (block argument). -/
theorem avg_optimal_of_pathwise_regret {S A Ω : Type} [Countable S] [Countable Ω]
    (demand : PMF Ω) (step : S → A → Ω → S) (cost : S → A → Ω → ENNReal)
    (f : S → A) (σ : MarkovPolicy S A) (s₀ : S) (F : Set S) (B C : ENNReal)
    (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hs₀ : s₀ ∈ F)
    (hF : ∀ s ∈ F, ∀ ω, step s (f s) ω ∈ F)
    (hcost : ∀ s ∈ F, ∀ ω, cost s (f s) ω ≤ B)
    (hpath : ∀ (w : ℕ → Ω) (x : S), x ∈ F → ∀ (u v : ℕ → S), u 0 = x → v 0 = s₀ →
      (∀ t, u (t + 1) = step (u t) (f (u t)) (w t)) →
      (∀ t, v (t + 1) = step (v t) (σ t (v t)) (w t)) →
      ∀ T, ∑ t ∈ Finset.range T, cost (u t) (f (u t)) (w t) ≤
        ∑ t ∈ Finset.range T, cost (v t) (σ t (v t)) (w t) + C) :
    controlledAvgUpper demand step cost (fun _ => f) s₀ ≤
      controlledAvgLower demand step cost σ s₀ := by sorry

end PerishShip.Waste
