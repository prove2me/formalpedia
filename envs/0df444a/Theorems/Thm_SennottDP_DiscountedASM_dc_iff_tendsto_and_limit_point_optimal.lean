-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_dc_iff_tendsto_and_limit_point_optimal
-- name    : SennottDP.DiscountedASM.dc_iff_tendsto_and_limit_point_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T08:00:11.452347+00:00
-- url     : https://prove2.me/theorems/0c0874f1-9abb-45b4-bb61-8e0e28865059
-- title:
--   Theorem 4.6.3 — DC($\alpha$) iff $V^N_\alpha\to V_\alpha<\infty$; limit points of $\Delta_N$-optimal policies are optimal
-- statement:
--   Let $\Delta$ be an MDC with countable state space $S$, let $(\Delta_N)_{N\ge N_0}$ be an approximating sequence for $\Delta$, and fix $\alpha\in(0,1)$. Let $V_\alpha$ be the discounted value function of $\Delta$ and $V^N_\alpha$ that of $\Delta_N$. The following are equivalent:
--
--   1. $\lim_{N\to\infty}V^N_\alpha(i)=V_\alpha(i)<\infty$ for every $i\in S$.
--   2. Assumption DC($\alpha$) holds.
--
--   Assume that either (then both) holds. For each $N\ge N_0$ let $f^N_\alpha$ be a stationary policy of $\Delta_N$ that realizes the minimum in the discount optimality equation of $\Delta_N$,
--   $$
--   V^N_\alpha(i)=\min_{a\in A_i}\Big\{C(i,a)+\alpha\sum_{j\in S_N}P_{ij}(a;N)\,V^N_\alpha(j)\Big\},\qquad i\in S_N. \tag{4.36}
--   $$
--   Then every limit point $f$ of the sequence $(f^N_\alpha)_{N\ge N_0}$ is discount optimal for $\Delta$: $V_{f,\alpha}(i)=V_\alpha(i)$ for all $i\in S$.
--
--   This is the main theorem of the approximating sequence method for the discounted criterion: optimal policies of the finite truncations, which can be computed, converge along subsequences to an optimal stationary policy of the countable-state problem exactly when DC($\alpha$) holds.
--
--   **Formalization Note** $V^N_\alpha$ is the value function of $\Delta_N$ as an MDC on $S_N$, extended by $0$ outside $S_N$ (which no limit in $N$ sees). "$f^N_\alpha$ realizes the minimum in (4.36)" is stated as: $f^N_\alpha(i)\in A_i$ and its bracket is at most the bracket of every $a\in A_i$, for all $N\ge N_0$ and $i\in S_N$. A limit point is in the sense of Definition B.4. Optimality of $f$ compares the discounted cost of $f$ viewed as a general policy with the infimum over all history-dependent randomized policies.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 76, Theorem 4.6.3; p. 75, equation (4.36)

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Theorem 4.6.3 (p. 76). (i) `V^N_α → V_α < ∞` pointwise iff (ii) Assumption DC(α).
Under either, if `f^N_α` is a stationary policy of `Δ_N` realizing the minimum in the discount
optimality equation (4.36) of `Δ_N`, then every limit point of `(f^N_α)_{N ≥ N₀}` is discount
optimal for `M`. -/
theorem dc_iff_tendsto_and_limit_point_optimal {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    ((∀ i, M.value α i < ⊤ ∧
        Tendsto (fun N => Δs.VN α N i) atTop (𝓝 (M.value α i))) ↔ Δs.DC α) ∧
    (Δs.DC α → ∀ fN : ℕ → S → Act,
      (∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, fN N i ∈ M.A i ∧
        ∀ a ∈ M.A i,
          (M.C i (fN N i) : ℝ≥0∞) +
              (α : ℝ≥0∞) * ∑ j ∈ Δs.SN N, Δs.PN N i (fN N i) j * Δs.VN α N j ≤
            (M.C i a : ℝ≥0∞) + (α : ℝ≥0∞) * ∑ j ∈ Δs.SN N, Δs.PN N i a j * Δs.VN α N j) →
      ∀ (f : S → Act) (hf : ∀ i, f i ∈ M.A i), Δs.IsLimitPoint fN f →
        ∀ i, MDC.discCost (M.ofStationary f hf) α i = M.value α i) := by sorry

end SennottDP.DiscountedASM
