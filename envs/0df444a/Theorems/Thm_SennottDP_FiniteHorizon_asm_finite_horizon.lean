-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_asm_finite_horizon
-- name    : SennottDP.FiniteHorizon.asm_finite_horizon
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:38:03.241604+00:00
-- url     : https://prove2.me/theorems/8a9929dc-a6a6-47b6-bb09-f34f8d3b437c
-- title:
--   Theorem 3.2.3 — FH(α, n) iff $v^N_{\alpha,n} \to v_{\alpha,n} < \infty$; limit points of optimal policies of $\Delta_N$ are optimal
-- statement:
--   Let $(\Delta_N)$ be an approximating sequence for the MDC $\Delta$ (countable state space, terminal cost $F$), let $0 < \alpha \le 1$ and fix $n \ge 1$. The following are equivalent:
--
--   1. $\lim_{N\to\infty} v^N_{\alpha,n}(i) = v_{\alpha,n}(i) < \infty$ for every $i \in S$;
--   2. Assumption FH($\alpha$, $n$) holds: $\limsup_{N\to\infty} v^N_{\alpha,n}(i) < \infty$ and $\limsup_{N\to\infty} v^N_{\alpha,n}(i) \le v_{\alpha,n}(i)$ for every $i \in S$.
--
--   Assume that either (then both) of these holds, and let $e^N_n$ be a stationary policy for $\Delta_N$ that is optimal for the $n$ horizon at time $t = 0$, i.e. $e^N_n(i) \in B^N_i(\alpha,n)$ for all $i \in S_N$. Then every limit point $e_n$ of $(e^N_n)_{N \ge N_0}$ is optimal in $\Delta$ for the $n$ horizon at $t = 0$:
--   $$
--   e_n(i) \in B_i(\alpha,n) \qquad \text{for all } i \in S .
--   $$
--
--   This is the justification of the approximating sequence method for finite horizons: finite truncations compute the value function and the first decision of an optimal policy of the countable-state chain exactly when FH holds.
--
--   **Formalization Note** "Optimal for the $n$ horizon at time $t = 0$" is expressed through the minimizing sets, as in Corollary 3.1.4: a stationary policy with $e(i) \in B_i(\alpha,n)$ for all $i$ is the first decision of an $n$ horizon optimal deterministic Markov policy. $v^N_{\alpha,n}(i)$ is `valueN`, set to $0$ for the finitely many $N$ with $N < N_0$ or $i \notin S_N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 43, Theorem 3.2.3 (proof pp. 43–44)

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Theorem 3.2.3 (Sennott, pp. 43–44). Let `(Δ_N)` be an approximating sequence for `Δ`, with
the terminal cost `F` of `Δ`, `0 < α ≤ 1`, and let `n ≥ 1` be fixed. The following are
equivalent: (i) `lim_{N → ∞} v^N_{α,n}(i) = v_{α,n}(i) < ∞` for every `i ∈ S`;
(ii) Assumption FH(α, n) holds. If either holds, and `e^N_n` is a stationary policy for `Δ_N` that
is optimal for the `n` horizon at time `t = 0` (`e^N_n(i) ∈ B^N_i(α, n)` for all `i ∈ S_N`,
`N ≥ N₀`), then any limit point `e_n` of `(e^N_n)_{N ≥ N₀}` is optimal in `Δ` for the `n`
horizon at `t = 0`: `e_n(i) ∈ B_i(α, n)` for all `i ∈ S`. -/
theorem asm_finite_horizon {S Act : Type} [Countable S] (M : MDC S Act) (F : S → ℝ≥0)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1) (AS : M.ApproxSeq) (n : ℕ) (hn : 1 ≤ n) :
    ((∀ i, Tendsto (fun N => AS.valueN F α n N i) atTop (𝓝 (M.value F α n i)) ∧
        M.value F α n i < ⊤) ↔ AS.FH F α n) ∧
    (AS.FH F α n → ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N (hN : AS.N₀ ≤ N) (i : AS.SN N), e N i.1 ∈ AS.minSetN F α n N hN i) →
      ∀ f : M.Stationary, M.IsApproxLimitPoint e f → ∀ i, f.1 i ∈ M.minSet F α n i) := by sorry

end SennottDP.FiniteHorizon
