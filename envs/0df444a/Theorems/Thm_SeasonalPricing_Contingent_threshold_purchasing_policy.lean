-- Prove2me | Theorems.Thm_SeasonalPricing_Contingent_threshold_purchasing_policy
-- name    : SeasonalPricing.Contingent.threshold_purchasing_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:11:02.562431+00:00
-- url     : https://prove2.me/theorems/f7a55159-9377-45cc-a8ba-8ac1fe156426
-- title:
--   Theorem 1 and Corollary 1 — the optimal purchasing policy is an increasing threshold on the current valuation
-- statement:
--   A seller holds $Q$ units over a season $[0, H]$ with premium price $p_1 \ge 0$ on $[0, T)$ and a contingent discount menu $p_2(1), \dots, p_2(Q)$ with $p_2(q) \le p_1$, charged from $T$ on according to the remaining inventory. A customer's valuation declines as $V(t) = V e^{-\alpha t}$ with $\alpha \ge 0$. Let $(\pi, a)$ be an arbitrary belief of the customers about the remaining inventory $Q_T$ and the allocation event $\mathcal A$ (this belief encodes arbitrary purchasing strategies of the other customers). For $t \in [0, T)$ write
--
--   $$
--   W_t(\psi) = \mathrm E_{Q_T}\!\left[\max\{\psi e^{-\alpha(T-t)} - p_2(Q_T), 0\}\cdot \mathbf 1\{\mathcal A \mid Q_T\}\right].
--   $$
--
--   Assume $\alpha > 0$ or $\sum_{q=0}^{Q} \pi(q) a(q) < 1$. Then:
--
--   1. **(Theorem 1, the threshold.)** For every $t \in [0, T)$ the implicit equation (2), $\psi - p_1 = W_t(\psi)$, has a unique solution $\psi(t) \in [p_1, \infty)$.
--   2. **(Theorem 1, optimality of the threshold policy.)** For every $t \in [0, T)$, a customer arriving at $t$ with current valuation $V(t)$ buys immediately under the paper's rule (nonnegative current surplus $V(t) - p_1$, at least the expected surplus of waiting $W_t(V(t))$) if and only if $V(t) \ge \psi(t)$.
--   3. **(Corollary 1.)** The threshold function $\psi : [0, T) \to [p_1, \infty)$ is increasing in $t$: if $\psi(t)$ solves (2) with $\psi(t) \ge p_1$ for every $t \in [0,T)$, then $t \le t'$ implies $\psi(t) \le \psi(t')$.
--
--   Theorem 1 is the central structural result of the paper: forward-looking customers, whatever the others do, use a time-dependent threshold on their current valuation, which is what makes the seller's contingent-pricing problem and the equilibrium computation of §§4.2–4.3 finite-dimensional.
--
--   **Formalization Note** Only the branch $0 \le t < T$ of the threshold function $\theta$ is formalized; for $T \le t \le H$ the paper's $\theta(t) = p_2$ is the model's own rule for late customers ("buy iff a nonnegative surplus is available now"), with no content to prove. Part 2 is the paper's "it is optimal to base their purchasing decisions on a threshold function": the optimal (surplus-maximizing) decision is the rule (i)–(ii) of p. 344, and part 2 shows it equals $V(t) \ge \psi(t)$. The paper writes "increasing"; $\psi$ is constant on an initial interval whenever no menu price is reachable (p. 347), so part 3 asserts nondecreasing. Two hypotheses are additions: "$\alpha > 0$ or $\sum \pi a < 1$" (the paper's slope bound "$< 1$" fails when $\alpha = 0$ and allocation is sure), and $p_1 \ge 0$ (prices are nonnegative in the model; without it Corollary 1 fails, e.g. $p_1 = p_2 = -1$). The belief does not depend on $t$, as in Eq. (4).
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 344, Theorem 1, Eqs. (1)–(2); p. 345, Corollary 1

import Mathlib
import Definitions.Def_SeasonalPricing_Contingent_IsInventoryBelief
import Definitions.Def_SeasonalPricing_Contingent_waitingSurplus

namespace SeasonalPricing.Contingent

/-- Theorem 1 and Corollary 1 (Aviv–Pazgal 2008, pp. 344–345), branch `0 ≤ t < T`.
Fix a pricing scheme `{p₁, p₂(1), …, p₂(Q)}` with `p₂(q) ≤ p₁` and a customer belief
(`pmf`, `alloc`) about the remaining inventory `Q_T` and the allocation event 𝒜.
(a) for every `t ∈ [0, T)` equation (2) has a unique solution `ψ(t) ∈ [p₁, ∞)`;
(b) the purchase rule of p. 344 is the threshold rule "buy now iff `V(t) ≥ ψ(t)`";
(c) the threshold function `ψ : [0, T) → [p₁, ∞)` is (weakly) increasing in `t`. -/
theorem threshold_purchasing_policy (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (p1 α T : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) (hα : 0 ≤ α) (hT : 0 < T)
    (hp1 : 0 ≤ p1) (hp2 : ∀ q ∈ Finset.Icc 1 Q, p2 q ≤ p1)
    (hslope : 0 < α ∨ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q < 1) :
    (∀ t ∈ Set.Ico 0 T,
      ∃! ψ : ℝ, p1 ≤ ψ ∧ ψ - p1 = waitingSurplus Q pmf alloc p2 α T t ψ) ∧
    (∀ t ∈ Set.Ico 0 T, ∀ ψ : ℝ,
      p1 ≤ ψ → ψ - p1 = waitingSurplus Q pmf alloc p2 α T t ψ →
      ∀ v : ℝ, buysNow Q pmf alloc p2 p1 α T t v ↔ ψ ≤ v) ∧
    (∀ ψ : ℝ → ℝ,
      (∀ t ∈ Set.Ico 0 T,
        p1 ≤ ψ t ∧ ψ t - p1 = waitingSurplus Q pmf alloc p2 α T t (ψ t)) →
      MonotoneOn ψ (Set.Ico 0 T)) := by sorry

end SeasonalPricing.Contingent
