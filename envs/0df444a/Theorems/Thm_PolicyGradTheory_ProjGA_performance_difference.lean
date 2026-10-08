-- Prove2me | Theorems.Thm_PolicyGradTheory_ProjGA_performance_difference
-- name    : PolicyGradTheory.ProjGA.performance_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:19:43.221301+00:00
-- url     : https://prove2.me/theorems/4b7aa51f-a0fb-40c0-af4a-82fc08ead837
-- title:
--   Lemma 3.2, p. 12 — performance difference: V^π(s₀) − V^{π′}(s₀) = (1/(1−γ)) E_{s∼d^π_{s₀}} E_{a∼π(·|s)}[A^{π′}(s,a)]
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$. For a policy $\pi$ and a state $s_0$, write $d^\pi_{s_0}$ for the discounted state visitation distribution of $\pi$ started at $s_0$, and $A^{\pi'}(s,a)=Q^{\pi'}(s,a)-V^{\pi'}(s)$ for the advantage of $\pi'$.
--
--   **Lemma (performance difference, Kakade–Langford).** For all policies $\pi,\pi'$ and all states $s_0$,
--   $$
--   V^\pi(s_0)-V^{\pi'}(s_0)=\frac1{1-\gamma}\,\mathbb E_{s\sim d^\pi_{s_0}}\,\mathbb E_{a\sim\pi(\cdot\mid s)}\big[A^{\pi'}(s,a)\big].
--   $$
--
--   The identity expresses the value gap between two policies through the advantage of one of them under the state distribution of the other. In this paper it is the first step of the gradient domination lemma (Lemma 4.1) and of the analyses of all later algorithms.
--
--   **Formalization Note** The expectations are written as finite sums, $\sum_s d^\pi_{s_0}(s)\sum_a\pi(a\mid s)A^{\pi'}(s,a)$, with $d^\pi_{s_0}$ the visitation distribution of the point mass at $s_0$.
-- source:
--   arXiv:1908.00261v5, Lemma 3.2, p. 12 (proof in App. A, p. 48)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Lemma 3.2 (performance difference lemma), arXiv:1908.00261v5, p. 12: for all policies `π, π'`
and states `s₀`, `V^π(s₀) − V^{π'}(s₀) = (1/(1−γ)) E_{s∼d^π_{s₀}} E_{a∼π(·|s)} [A^{π'}(s,a)]`,
where `d^π_{s₀}` is the visitation distribution started from the point mass at `s₀`. -/
theorem performance_difference {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s₀ : S) :
    PolicyValue π P r γ s₀ - PolicyValue π' P r γ s₀ =
      1 / (1 - γ) * ∑ s, visitation π P γ (fun x => if x = s₀ then 1 else 0) s *
        ∑ a, π s a * advantage π' P r γ s a := by sorry

end PolicyGradTheory.ProjGA
