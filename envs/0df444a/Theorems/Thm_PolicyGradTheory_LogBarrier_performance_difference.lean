-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_performance_difference
-- name    : PolicyGradTheory.LogBarrier.performance_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:37.418208+00:00
-- url     : https://prove2.me/theorems/cc685e70-cb56-4277-85f1-777d1730a728
-- title:
--   Lemma 3.2, p. 12 — performance difference: V^π(s₀) − V^{π'}(s₀) = (1/(1−γ)) E_{s∼d^π_{s₀}} E_{a∼π(·|s)} A^{π'}(s,a)
-- statement:
--   This is the performance difference lemma of Kakade and Langford (2002), in the unnormalized convention of the paper.
--
--   Let $(P,r,\gamma)$ be a finite MDP with $r\in[0,1]$ and $\gamma\in[0,1)$. For all policies $\pi,\pi'$ and every state $s_0$,
--   $$
--   V^\pi(s_0)-V^{\pi'}(s_0)=\frac{1}{1-\gamma}\,\mathbb E_{s\sim d^\pi_{s_0}}\,\mathbb E_{a\sim\pi(\cdot\mid s)}\big[A^{\pi'}(s,a)\big],
--   $$
--   where $d^\pi_{s_0}$ is the discounted state visitation distribution (4) of $\pi$ started at $s_0$ and $A^{\pi'}=Q^{\pi'}-V^{\pi'}$ is the advantage of $\pi'$.
--
--   The lemma converts a gap in values into an average of advantages under the visitation of the comparison policy; the proof of Theorem 5.2 applies it with $\pi=\pi^\star$ and $\pi'=\pi_\theta$.
--
--   **Formalization Note.** $d^\pi_{s_0}$ is the visitation with the point mass at $s_0$ as start distribution, and both expectations are finite sums. The same identity in the normalized convention $(1-\gamma)V$ is posed as `ApproxOptRL.*.performance_difference`.
-- source:
--   arXiv:1908.00261v5, Lemma 3.2, p. 12

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.LogBarrier

/-- Lemma 3.2 (the performance difference lemma), arXiv:1908.00261v5, p. 12:
`V^π(s₀) − V^{π'}(s₀) = (1/(1−γ)) E_{s∼d^π_{s₀}} E_{a∼π(·|s)} [A^{π'}(s,a)]`,
where `d^π_{s₀}` is the discounted state PolicyGradTheory.ProjGA.visitation (4) started from the point mass at `s₀`. -/
theorem performance_difference {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s₀ : S) :
    PolicyValue π P r γ s₀ - PolicyValue π' P r γ s₀ =
      1 / (1 - γ) * ∑ s, PolicyGradTheory.ProjGA.visitation π P γ (fun s' => if s' = s₀ then 1 else 0) s *
        ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a := by sorry

end PolicyGradTheory.LogBarrier
