-- Prove2me | Theorems.Thm_SampleComplexityRL_Mismeasure_per_state_error_le_two_regression
-- name    : SampleComplexityRL.Mismeasure.per_state_error_le_two_regression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:08.98583+00:00
-- url     : https://prove2.me/theorems/13a30a75-2b70-44f2-aced-c79362043250
-- title:
--   Proof of Theorem 5.3.2, p. 64 — a decision rule greedy for Q̃ has per state error ε_t(s) ≤ 2ε̃_t(s)
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P$ a transition kernel, $r:S\times A\to[0,1]$ a reward function and $T\ge1$. Let $\pi$ be a deterministic policy (the input to RegressionPolicyChooser at update $t$), let $\tilde Q:S\times A\to\mathbb R$ be any approximation of $Q_{\pi,t}$, and let $h_t$ be a decision rule greedy with respect to $\tilde Q$, i.e. $\tilde Q(s,a)\le\tilde Q(s,h_t(s))$ for all $s,a$. Then for every state $s$,
--   $$\varepsilon_t(s)=\max_{a\in A}Q_{\pi,t}(s,a)-Q_{\pi,t}(s,h_t(s))\;\le\;2\max_{a\in A}\big|Q_{\pi,t}(s,a)-\tilde Q(s,a)\big|=2\,\tilde\varepsilon_t(s).$$
--
--   This converts the regression error of RegressionPolicyChooser into the per state error that Lemma 5.3.1 relates to the advantages of NAPI's output policy.
--
--   **Formalization Note** Greediness is the relation $\tilde Q(s,a)\le\tilde Q(s,h_t(s))$ for all $s,a$, so the statement holds for every tie-breaking rule.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 64, display in the proof of Theorem 5.3.2

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
import Definitions.Def_SampleComplexityRL_Mismeasure_NAPI
open FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.Mismeasure

/-- **Display in the proof of Theorem 5.3.2** (Kakade 2003, p. 64). Let `π` be a deterministic
input policy to RegressionPolicyChooser at update `t`, let `Q̃` approximate `Q_{π,t}`, and let the
returned decision rule `h_t` be greedy with respect to `Q̃` (`Q̃(s,a) ≤ Q̃(s,h_t(s))` for all
`s`, `a`). Then for every state `s`, `ε_t(s) ≤ 2 ε̃_t(s)`, where
`ε_t(s) = max_a Q_{π,t}(s,a) - Q_{π,t}(s,h_t(s))` and `ε̃_t(s) = max_a |Q_{π,t}(s,a) - Q̃(s,a)|`. -/
theorem per_state_error_le_two_regression {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (T : ℕ) (hT : 0 < T)
    (π : ℕ → S → A) (t : ℕ) (Qtil : S → A → ℝ) (ht : S → A)
    (hgreedy : ∀ s a, Qtil s a ≤ Qtil s (ht s)) (s : S) :
    perStateError P r T π t ht s ≤ 2 * regressionError P r T π t Qtil s := by sorry

end SampleComplexityRL.Mismeasure
