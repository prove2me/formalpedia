-- Prove2me | Theorems.Thm_PolicyGradTheory_NPG_performance_difference
-- name    : PolicyGradTheory.NPG.performance_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:09:39.853487+00:00
-- url     : https://prove2.me/theorems/1c9adaff-6916-47d7-bf0f-146583e99827
-- title:
--   Lemma 3.2, p. 12 — performance difference: V^π(s₀) − V^{π′}(s₀) = (1/(1−γ)) E_{s∼d^π_{s₀}} E_{a∼π(·|s)}[A^{π′}(s,a)]
-- statement:
--   This is the performance difference lemma of Kakade and Langford, in the unnormalized convention of the paper.
--
--   Let $(P,r,\gamma)$ be a finite MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$. For a state $s_0$, let $d^\pi_{s_0}$ be the discounted state visitation distribution of $\pi$ started at $s_0$, and let $A^{\pi'}(s,a)=Q^{\pi'}(s,a)-V^{\pi'}(s)$ be the advantage of $\pi'$. Then for all policies $\pi,\pi'$ and every state $s_0$,
--   $$
--   V^\pi(s_0)-V^{\pi'}(s_0)=\frac{1}{1-\gamma}\,\mathbb E_{s\sim d^\pi_{s_0}}\,\mathbb E_{a\sim\pi(\cdot\mid s)}\big[A^{\pi'}(s,a)\big].
--   $$
--
--   The lemma expresses the value gap between two policies as the advantage of one policy, averaged along the states visited by the other. In the analysis of natural policy gradient it is applied twice: with $\pi'=\pi^{(t)}$ and $\pi=\pi^{(t+1)}$ (improvement), and with $\pi=\pi^\star$ (regret against the optimum).
--
--   **Formalization Note** $d^\pi_{s_0}$ is the visitation distribution started from the point mass at $s_0$. The same identity is posed elsewhere on the platform in Kakade–Langford's normalized convention ($(1-\gamma)V$); it is restated here in the paper's convention.
-- source:
--   arXiv:1908.00261v5, Lemma 3.2, p. 12

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.NPG

/-- Lemma 3.2 (performance difference lemma; arXiv:1908.00261v5, p. 12): for all policies
`π, π'` and states `s₀`,
`V^π(s₀) − V^{π'}(s₀) = 1/(1−γ) E_{s∼d^π_{s₀}} E_{a∼π(·|s)} [A^{π'}(s,a)]`. -/
theorem performance_difference {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s₀ : S) :
    PolicyValue π P r γ s₀ - PolicyValue π' P r γ s₀ =
      1 / (1 - γ) * ∑ s, PolicyGradTheory.ProjGA.visitation π P γ (fun x => if x = s₀ then 1 else 0) s *
        ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a := by sorry

end PolicyGradTheory.NPG
