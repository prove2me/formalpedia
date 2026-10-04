-- Prove2me | Theorems.Thm_SennottDP_Discounted_discounted_tail_tendsto_zero
-- name    : SennottDP.Discounted.discounted_tail_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T07:08:47.791057+00:00
-- url     : https://prove2.me/theorems/e5ce1898-2cb2-40ea-a187-3c61aeb7af99
-- title:
--   Corollary 4.1.5 — $\alpha^n E_{f_\alpha}[V_\alpha(X_n)] \to 0$ at states with finite value
-- statement:
--   Let $\Delta$ be a Markov decision chain and $\alpha \in (0,1)$. Let $f_\alpha$ be a stationary policy realizing the minimum in the discount optimality equation (4.9), and let $i$ be a state with $V_\alpha(i) < \infty$. Then
--   $$\lim_{n \to \infty} \alpha^n E_{f_\alpha}[V_\alpha(X_n) \mid X_0 = i] = 0. \tag{4.12}$$
--
--   The discounted value of the state reached at time $n$ under the optimal stationary policy thus vanishes; this is the transversality property used to identify $V_\alpha$ among the solutions of (4.9).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 64, Corollary 4.1.5, (4.12)

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Corollary 4.1.5, p. 64: if `V_α(i) < ∞` and `f_α` is a stationary policy
realizing the minimum in the discount optimality equation (4.9), then
`lim_{n→∞} α^n E_{f_α}[V_α(X_n) | X_0 = i] = 0` (4.12). -/
theorem discounted_tail_tendsto_zero {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (f : StationaryPolicy M)
    (hf : Realizes M f α (valueFn M α)) (i : S) (hi : valueFn M α i < ⊤) :
    Tendsto (fun n : ℕ => (α : ℝ≥0∞) ^ n * expState M f.toPolicy i n (valueFn M α)) atTop
      (𝓝 0) := by sorry

end SennottDP.Discounted
