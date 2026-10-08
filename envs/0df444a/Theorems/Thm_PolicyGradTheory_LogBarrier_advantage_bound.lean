-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_advantage_bound
-- name    : PolicyGradTheory.LogBarrier.advantage_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:25.884023+00:00
-- url     : https://prove2.me/theorems/a2af0975-727d-4d0b-ab09-dc1bccfda04b
-- title:
--   Proof of Theorem 5.2, p. 20 — at an ε_opt-stationary point of L_λ, max_a A^{π_θ}(s,a) ≤ 2λ/(µ(s)|S|)
-- statement:
--   Let $(P,r,\gamma)$ be a finite MDP, $\mu\in\Delta(\mathcal S)$, $\lambda>0$, and let $\theta$ satisfy
--   $$
--   \|\nabla_\theta L_\lambda(\theta)\|_2\le\epsilon_{\mathrm{opt}},\qquad \epsilon_{\mathrm{opt}}\le\frac{\lambda}{2|\mathcal S|\,|\mathcal A|}.
--   $$
--   Then for every state $s$ and action $a$,
--   $$
--   \mu(s)\,A^{\pi_\theta}(s,a)\le\frac{2\lambda}{|\mathcal S|},
--   $$
--   that is, $\max_a A^{\pi_\theta}(s,a)\le 2\lambda/(\mu(s)|\mathcal S|)$ wherever $\mu(s)>0$.
--
--   This is the claim the proof of Theorem 5.2 opens with; combined with the performance difference lemma it gives the theorem.
--
--   **Formalization Note.** The page divides by $\mu(s)$; the statement is multiplied through by $\mu(s)\ge 0$, so it is meaningful (and trivial) also at states with $\mu(s)=0$. The positivity $\lambda>0$ is implicit on the page ("a regularization parameter") and is stated explicitly.
-- source:
--   arXiv:1908.00261v5, §5.2, proof of Theorem 5.2, first sentence, p. 20

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.LogBarrier

/-- The claim the proof of Theorem 5.2 opens with (arXiv:1908.00261v5, §5.2, p. 20):
at an approximate stationary point of `L_λ`, `max_a A^{π_θ}(s,a) ≤ 2λ/(µ(s)|S|)` for all
states, stated multiplied through by `µ(s)`. -/
theorem advantage_bound {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (lam : ℝ) (hlam : 0 < lam) (εopt : ℝ)
    (θ : EuclideanSpace ℝ (S × A))
    (hgrad : ‖gradient (logBarrierObj P r γ μ lam) θ‖ ≤ εopt)
    (hεopt : εopt ≤ lam / (2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ))) :
    ∀ s a, μ s * PolicyGradTheory.ProjGA.advantage (PolicyGradTheory.Softmax.softmaxPolicy θ) P r γ s a ≤ 2 * lam / (Fintype.card S : ℝ) := by sorry

end PolicyGradTheory.LogBarrier
