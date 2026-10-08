-- Prove2me | Theorems.Thm_SampleComplexityRL_ApproxDP_backup_contraction
-- name    : SampleComplexityRL.ApproxDP.backup_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:28.963438+00:00
-- url     : https://prove2.me/theorems/51e2392f-2c5d-4a5f-b94b-e4a86f569643
-- title:
--   §2.3.1, p. 26 — the normalized backup operator is a γ-contraction in max norm: ‖BJ − BJ′‖∞ ≤ γ‖J − J′‖∞
-- statement:
--   Let $S$ and $A$ be finite sets ($A$ nonempty), $P(\cdot\mid s,a)$ a transition kernel on $S$, $r:S\times A\to[0,1]$ a reward function and $0\le\gamma<1$. Let $B$ be the normalized backup operator
--   $[BJ](s)=\max_{a}\big((1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[J(s')]\big)$. Then for all vectors $J,J'\in\mathbb R^S$,
--   $$
--   \|BJ-BJ'\|_\infty\le\gamma\,\|J-J'\|_\infty,
--   $$
--   where $\|x\|_\infty=\max_s|x(s)|$.
--
--   This contraction property is the basic tool of the error analysis of value iteration and of its approximate version in §3.2.1.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is Mathlib's sup norm on the finite-dimensional space `S → ℝ`. The reward bound $r\in[0,1]$ is the thesis's standing assumption and is carried for uniformity although the inequality does not use it.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 26, Section 2.3.1 (display: contraction property of B)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_ApproxDP_Greedy
open FoundationsML.ReinforcementLearning ApproxOptRL.Shared ApproxOptRL.PolicyQuality

namespace SampleComplexityRL.ApproxDP

/-- Kakade 2003, §2.3.1, p. 26: the backup operator is a γ-contraction in max norm. -/
theorem backup_contraction
    {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (J J' : S → ℝ) :
    ‖backup P r γ J - backup P r γ J'‖ ≤ γ * ‖J - J'‖ := by sorry

end SampleComplexityRL.ApproxDP
