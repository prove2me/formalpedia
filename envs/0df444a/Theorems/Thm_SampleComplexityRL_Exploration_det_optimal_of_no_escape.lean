-- Prove2me | Theorems.Thm_SampleComplexityRL_Exploration_det_optimal_of_no_escape
-- name    : SampleComplexityRL.Exploration.det_optimal_of_no_escape
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:10.983456+00:00
-- url     : https://prove2.me/theorems/13632210-df41-4b16-9176-53bce0c88a3d
-- title:
--   Proof of Theorem 8.3.5, p. 114 — in a deterministic MDP a non-escaping optimal policy of M_K is T-step optimal in M
-- statement:
--   Let $M$ be a deterministic MDP with finite state set $S$, finite nonempty action set $A$, next-state map $f$ and rewards $r(s,a)\in[0,1]$. Let $K\subseteq S$, let $M_K$ be the induced MDP and let $\pi$ be a $T$-step optimal policy in $M_K$. If, from state $s$ at time $t<T$, following $\pi$ in $M$ does not escape from $K$,
--   $$
--   \Pr(\text{escape from }K\mid\pi,M,s_t=s)=0,
--   $$
--   then $\pi$ is $T$-step optimal in $M$ at $(s,t)$:
--   $$
--   U_{\pi,t,M}(s)=U^*_{t,M}(s).
--   $$
--
--   This is the second fact behind the proof of Theorem 8.3.5: every step at which $R_{max}$ (with $m=1$) does not explore is spent executing a $T$-step optimal policy.
--
--   **Formalization Note** Epochs are 0-based, values carry the factor $1/T$, and $U^*_{t,M}$ is the supremum over all $T$-step policies.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 114, proof of Theorem 8.3.5 (last sentence)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_SampleComplexityRL_Exploration_Model

namespace SampleComplexityRL.Exploration

/-- **Non-escaping steps are optimal** (Kakade 2003, proof of Theorem 8.3.5, p. 114: "All other
steps must be spent executing `T`-step optimal policies"). Let `M` be a deterministic MDP with
next-state map `f` and rewards `r` in `[0,1]`, `K` a set of states and `π` an optimal `T`-step
policy in the induced MDP `M_K`. If following `π` from state `s` at time `t < T` does not escape
from `K` (escape probability `0`), then `π` is `T`-step optimal in `M` at `(s, t)`:
`U_{π,t,M}(s) = U*_{t,M}(s)`. -/
theorem det_optimal_of_no_escape {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (f : S → A → S) (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (K : Finset S) (T : ℕ) (π : ℕ → S → A)
    (hπ : IsTStepOptimal (inducedP (detKernel f) K) (inducedR r K) T π)
    (t : ℕ) (ht : t < T) (s : S)
    (hesc : escapeProb (detKernel f) K T π t s = 0) :
    uValue (detKernel f) r T π t s = optUValue (detKernel f) r T t s := by sorry

end SampleComplexityRL.Exploration
