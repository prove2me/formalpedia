-- Prove2me | Theorems.Thm_SampleComplexityRL_Exploration_deterministic_sample_complexity
-- name    : SampleComplexityRL.Exploration.deterministic_sample_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:58.982688+00:00
-- url     : https://prove2.me/theorems/5d77441e-b20c-40d0-950a-df85ee07d879
-- title:
--   Theorem 8.3.5 — one algorithm acts T-step optimally at all but NAT timesteps in every deterministic MDP
-- statement:
--   Fix a finite state set $S$ with $N=|S|$ states, a finite nonempty action set with $A$ actions, and a horizon $T\ge1$. There exists a single algorithm $\mathcal A$ — a deterministic function of the observed path $(s_0,a_0,r_0,\dots,s_t)$ of states, actions and rewards — with the following property. For every deterministic MDP on these states and actions (next-state map $f$, rewards $r(s,a)\in[0,1]$), every start state $s_0$ and every number of epochs $L$, the path $c$ produced by running $\mathcal A$ from $s_0$ satisfies
--   $$
--   U_{\mathcal A}(c_t)=U^*(c_t)
--   $$
--   for all but at most $NAT$ times $t<L$. Here $U_{\mathcal A}(c_t)=\frac1T\sum_{\tau=t}^{t'-1}r(s_\tau,a_\tau)$ is the normalized reward the algorithm collects from $t$ to the $T$-step end time $t'$ of $t$, and $U^*(c_t)$ is the best such reward any algorithm could collect from the same subpath.
--
--   The bound does not depend on $L$: however long the algorithm runs, it fails to act $T$-step optimally at most $NAT$ times. It is matched by the thesis's lower bound $\Omega(NAT)$ (Theorem 8.3.6).
--
--   **Formalization Note** The printed statement fixes the MDP before the algorithm ("Let $M$ be … There exists an algorithm"), which an algorithm knowing $M$ satisfies trivially. The thesis's algorithm ($R_{max}$ with $m=1$, p. 114) does not know $M$, and Theorem 8.3.1 says the algorithm takes only $N,A,T$ (and $\varepsilon,\delta$) as inputs; here the algorithm is chosen before the MDP, the start state and $L$. The algorithm observes rewards, as $R_{max}$ does (p. 105). Times are 0-based and counted for $t<L$ for every $L$, which is equivalent to the printed "$t\le L$". In a deterministic MDP the expectation in $U_{\mathcal A}$ is the realised sum, and $U^*(c_t)$ is the best normalized reward over action sequences of length $t'-t$ from $s_t$ (Markov property, p. 102).
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 104, Theorem 8.3.5 (definitions pp. 100, 102; algorithm pp. 108, 114)

import Mathlib
import Definitions.Def_SampleComplexityRL_Exploration_Online

namespace SampleComplexityRL.Exploration

/-- **Theorem 8.3.5 (Deterministic Sample Complexity)** (Kakade 2003, p. 104), uniform form.
Fix finite state and action sets `S`, `A` (`N = |S|`, `A = |A|`) and a horizon `T ≥ 1`. There is
one algorithm — a deterministic function of the observed state–action–reward path, chosen before
the MDP — such that for every deterministic MDP (next-state map `f`, rewards `r` in `[0,1]`), every
start state `s₀` and every number of epochs `L`, the run `c` of the algorithm satisfies
`U_A(c_t) = U*(c_t)` at all but at most `N·A·T` times `t < L`.

The printed statement reads "Let `M` be … There exists an algorithm `A`", i.e. `∀ M ∃ A`, which
is trivially satisfied by an algorithm that knows `M`; the thesis's algorithm (R_max with `m = 1`,
p. 114) does not know `M`, and Theorem 8.3.1 says the algorithm takes only `N, A, T` as inputs, so
the algorithm is quantified before the MDP. Rewards are part of the observed path (p. 105:
"Estimating the reward function is trivial"). -/
theorem deterministic_sample_complexity {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (T : ℕ) (hT : 0 < T) :
    ∃ alg : OnlineAlg S A,
      ∀ (f : S → A → S) (r : S → A → ℝ), (∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) →
        ∀ (s₀ : S) (L : ℕ),
          ((Finset.range L).filter
              (fun t => algValue f r T alg s₀ t ≠ optValue f r T alg s₀ t)).card
            ≤ Fintype.card S * Fintype.card A * T := by sorry

end SampleComplexityRL.Exploration
