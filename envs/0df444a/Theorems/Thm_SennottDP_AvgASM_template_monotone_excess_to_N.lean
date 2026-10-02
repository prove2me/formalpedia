-- Prove2me | Theorems.Thm_SennottDP_AvgASM_template_monotone_excess_to_N
-- name    : SennottDP.AvgASM.template_monotone_excess_to_N
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T09:43:16.310375+00:00
-- url     : https://prove2.me/theorems/95ad074a-e930-4367-beb0-288c57e4367a
-- title:
--   Corollary 8.2.2 — monotone value functions and excess probability sent to N
-- statement:
--   Let $\Delta$ have state space $S=\{0,1,2,\dots\}$ and let the approximating sequence $(\Delta_N)$ have state space $S_N=\{0,1,\dots,N\}$, obtained by sending the excess probability to $N$:
--   $$P_{ij}(a;N)=P_{ij}(a)+\mathbf 1\{j=N\}\sum_{r>N}P_{ir}(a),\qquad i,j\in S_N .$$
--   Assume that:
--   1. every stationary policy for $\Delta_N$ induces a unichain Markov chain with aperiodic positive recurrent class containing $0$;
--   2. for $n,N\ge1$ the value function $v^N_n(i)$ is increasing in $0\le i\le N$;
--   3. for $n\ge1$ the value function $v_n(i)$ is increasing in $i$;
--   4. there is a $0$ standard policy $d$ for $\Delta$ such that $m_{i0}(d)$ and $c_{i0}(d)$ are increasing in $i\ge1$.
--
--   Then the conclusions of Proposition 8.2.1 hold for $r^N(i)=\lim_{n\to\infty}\big(v^N_n(i)-v^N_n(0)\big)$: the value iteration algorithm is justified in each $\Delta_N$ and the (AC) assumptions hold.
--
--   This is the form of the template used for single-buffer queueing models, where monotonicity of the value functions in the queue length is available.
--
--   **Formalization Note** "Increasing" means nondecreasing. Conditions on $\Delta_N$ are imposed for $N\ge N_0$, where $\Delta_N$ is defined.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 174, Corollary 8.2.2

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Corollary 8.2.2** (Sennott 1999, p. 174). Let `Δ` have state space `S = {0, 1, 2, …}`, let
`(Δ_N)` have state space `S_N = {0, 1, …, N}`, and send the excess probability to `N`. Assume
(i) every stationary policy for `Δ_N` induces a unichain MC with aperiodic positive recurrent
class containing `0`; (ii) for `n, N ≥ 1`, `v^N_n(i)` is increasing in `0 ≤ i ≤ N`; (iii) for
`n ≥ 1`, `v_n(i)` is increasing in `i`; (iv) there is a `0` standard policy `d` for `Δ` such that
`m_{i0}(d)` and `c_{i0}(d)` are increasing in `i ≥ 1`. Then the conclusions of Proposition 8.2.1
hold for `r^N(i) = lim_{n→∞} (v^N_n(i) − v^N_n(0))`. -/
theorem template_monotone_excess_to_N {Act : Type*} {M : MDC ℕ Act} (AS : ApproxSeq M)
    (hSN : ∀ N, AS.N₀ ≤ N → AS.SN N = Finset.range (N + 1))
    (hexcess : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ j ∈ AS.SN N,
      AS.PN N i a j = M.P i a j + if j = N then ∑' r : {r : ℕ // N < r}, M.P i a r.1 else 0)
    (h1 : ∀ N (hN : AS.N₀ ≤ N), ∃ h0 : (0 : ℕ) ∈ AS.SN N,
      ∀ e : StationaryPolicy (AS.toMDC N hN), IsUnichainAperiodicWith e.chain ⟨0, h0⟩)
    (h2 : ∀ n N, 1 ≤ n → 1 ≤ N → AS.N₀ ≤ N → ∀ i j, i ≤ j → j ≤ N →
      AS.valueN n N i ≤ AS.valueN n N j)
    (h3 : ∀ n, 1 ≤ n → Monotone (horizonValue M n))
    (h4 : ∃ d : StationaryPolicy M, IsStandard d.chain d.cost 0 ∧
      ∀ i j, 1 ≤ i → i ≤ j →
        meanPassage d.chain {0} i ≤ meanPassage d.chain {0} j ∧
        passageCost d.chain d.cost {0} i ≤ passageCost d.chain d.cost {0} j) :
    AS.VIAAndAC 0 := by sorry

end SennottDP.AvgASM
