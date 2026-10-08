-- Prove2me | Theorems.Thm_SampleComplexityRL_Exploration_induced_inequalities
-- name    : SampleComplexityRL.Exploration.induced_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:13.167049+00:00
-- url     : https://prove2.me/theorems/1868de6b-a65f-4826-b008-23d20dd9d217
-- title:
--   Lemma 8.4.4 — induced inequalities: U_{π,t,M_K} ≥ U_{π,t,M} ≥ U_{π,t,M_K} − Pr(escape from K)
-- statement:
--   Let $M$ be an MDP with finite state set $S$, finite action set $A$, transition model $P$ and rewards $r(s,a)\in[0,1]$. Let $K\subseteq S$ be a set of states and $M_K$ the induced MDP, in which the states outside $K$ are absorbing with reward $1$. For every $T$-step policy $\pi$, every time $t<T$ and every state $s$,
--   $$
--   U_{\pi,t,M_K}(s)\ \ge\ U_{\pi,t,M}(s)
--   \qquad\text{and}\qquad
--   U_{\pi,t,M}(s)\ \ge\ U_{\pi,t,M_K}(s)-\Pr(\text{escape from }K\mid\pi,M,s_t=s).
--   $$
--   Here $U_{\pi,t,M}(s)$ is the normalized reward $\frac1T\mathbb E[\sum_{\tau=t}^{T-1}r(s_\tau,a_\tau)]$ of $\pi$ from $s_t=s$, and the escape probability is the probability that the path $(s_t,\dots,s_{T-1})$ of $\pi$ in $M$ visits a state outside $K$.
--
--   The first inequality says that $M_K$ is optimistic; the second that a policy which rarely leaves $K$ earns in $M$ nearly what it earns in $M_K$. Together they are the basis of the explore-or-exploit property of $R_{max}$.
--
--   **Formalization Note** Epochs are 0-based and values carry the factor $1/T$. The bound $r\le1$ is used: the reward $1$ of $M_K$ outside $K$ must dominate the rewards of $M$.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 107, Lemma 8.4.4

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_SampleComplexityRL_Exploration_Model

namespace SampleComplexityRL.Exploration

open FoundationsML.ReinforcementLearning

/-- **Lemma 8.4.4 (Induced Inequalities)** (Kakade 2003, p. 107). Let `M = (P, r)` be an MDP
with rewards in `[0,1]`, `K` a set of states and `M_K` the induced MDP. For every deterministic
`T`-step policy `π`, time `t < T` and state `s`,
`U_{π,t,M_K}(s) ≥ U_{π,t,M}(s)` and
`U_{π,t,M}(s) ≥ U_{π,t,M_K}(s) − Pr(escape from K | π, M, s_t = s)`. -/
theorem induced_inequalities {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (K : Finset S) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (ht : t < T) (s : S) :
    uValue P r T π t s ≤ uValue (inducedP P K) (inducedR r K) T π t s ∧
      uValue (inducedP P K) (inducedR r K) T π t s - escapeProb P K T π t s
        ≤ uValue P r T π t s := by sorry

end SampleComplexityRL.Exploration
