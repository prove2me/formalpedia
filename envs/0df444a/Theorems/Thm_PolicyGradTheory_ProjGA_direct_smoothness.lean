-- Prove2me | Theorems.Thm_PolicyGradTheory_ProjGA_direct_smoothness
-- name    : PolicyGradTheory.ProjGA.direct_smoothness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:45:11.390639+00:00
-- url     : https://prove2.me/theorems/76cd4b6b-f3ae-4c32-bc72-531f7ddf3492
-- title:
--   Lemma D.3, p. 74 — smoothness of the direct parameterization: ‖∇_πV^π(s₀) − ∇_πV^{π′}(s₀)‖₂ ≤ (2γ|A|/(1−γ)³)‖π − π′‖₂
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in[0,1)$. Under the direct parameterization, write $\nabla_\pi V^\pi(s_0)$ for the gradient of $\pi\mapsto V^\pi(s_0)$, the value from the start state $s_0$.
--
--   **Lemma (smoothness for direct parameterization).** For every start state $s_0$ and all policies $\pi,\pi'\in\Delta(\mathcal A)^{|\mathcal S|}$,
--   $$
--   \big\|\nabla_\pi V^\pi(s_0)-\nabla_\pi V^{\pi'}(s_0)\big\|_2\le\frac{2\gamma|\mathcal A|}{(1-\gamma)^3}\,\|\pi-\pi'\|_2 .
--   $$
--
--   So $V^\pi(s_0)$, and hence $V^\pi(\mu)$ for every start distribution $\mu$, is $\beta$-smooth on the policy simplex with $\beta=2\gamma|\mathcal A|/(1-\gamma)^3$. This constant fixes the step size $\eta=1/\beta$ of Theorem 4.1 and enters its iteration bound.
--
--   **Formalization Note** The value from $s_0$ is the objective with the point mass at $s_0$ as start distribution. As everywhere in Appendix D, $\pi,\pi'$ range over policies; the gradients are the full Euclidean gradients on `EuclideanSpace ℝ (S × A)`.
-- source:
--   arXiv:1908.00261v5, Lemma D.3, p. 74 (uses Lemma D.2, pp. 71–74)

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- Lemma D.3 (smoothness for direct parameterization), arXiv:1908.00261v5, p. 74: for all
starting states `s₀` and all policies `π, π'`,
`‖∇_π V^π(s₀) − ∇_π V^{π'}(s₀)‖₂ ≤ (2γ|A|/(1−γ)³) ‖π − π'‖₂`. -/
theorem direct_smoothness {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ) :
    ∀ (s₀ : S), ∀ π ∈ simplexSet S A, ∀ π' ∈ simplexSet S A,
      ‖gradient (directValue P r γ (fun x => if x = s₀ then 1 else 0)) π -
          gradient (directValue P r γ (fun x => if x = s₀ then 1 else 0)) π'‖ ≤
        2 * γ * (Fintype.card A : ℝ) / (1 - γ) ^ 3 * ‖π - π'‖ := by sorry

end PolicyGradTheory.ProjGA
