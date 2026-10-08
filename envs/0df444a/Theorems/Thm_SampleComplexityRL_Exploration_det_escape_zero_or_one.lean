-- Prove2me | Theorems.Thm_SampleComplexityRL_Exploration_det_escape_zero_or_one
-- name    : SampleComplexityRL.Exploration.det_escape_zero_or_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:50.449274+00:00
-- url     : https://prove2.me/theorems/0a747c70-11ed-40a2-ad62-a9e8a973cfc2
-- title:
--   Proof of Theorem 8.3.5, p. 114 — in a deterministic MDP every escape probability is 0 or 1
-- statement:
--   Let $M$ be a deterministic MDP with finite state set $S$ and next-state map $f$, so that $P(s'\mid s,a)=1$ if $s'=f(s,a)$ and $0$ otherwise. For every set of states $K$, every $T$-step policy $\pi$, every time $t$ and every state $s$,
--   $$
--   \Pr(\text{escape from }K\mid\pi,M,s_t=s)\in\{0,1\}.
--   $$
--   In the thesis's words, any attempted escape from $K$ succeeds with probability $1$: following $\pi$ from $s_t=s$ either surely leaves $K$ before time $T$ or surely stays in $K$.
--
--   This is the first of the two facts the proof of Theorem 8.3.5 uses: in a deterministic MDP every exploration attempt of $R_{max}$ reaches an unknown state.
--
--   **Formalization Note** The escape probability is $0$ for $t\ge T$ by definition.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 114, proof of Theorem 8.3.5 (second sentence)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_SampleComplexityRL_Exploration_Model

namespace SampleComplexityRL.Exploration

/-- **Deterministic escapes** (Kakade 2003, proof of Theorem 8.3.5, p. 114: "Since the MDP is
deterministic, any attempted escape from `K` in `t` steps succeeds with probability 1"). In a
deterministic MDP with next-state map `f`, for every deterministic `T`-step policy `π`, set of
states `K`, time `t` and state `s`, the escape probability
`Pr(escape from K | π, M, s_t = s)` is either `0` or `1`. -/
theorem det_escape_zero_or_one {S A : Type} [Fintype S] [DecidableEq S]
    (f : S → A → S) (K : Finset S) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (s : S) :
    escapeProb (detKernel f) K T π t s = 0 ∨ escapeProb (detKernel f) K T π t s = 1 := by sorry

end SampleComplexityRL.Exploration
