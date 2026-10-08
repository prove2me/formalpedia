-- Prove2me | Theorems.Thm_WhittleGittins_Retirement_theorem1_index_rule
-- name    : WhittleGittins.Retirement.theorem1_index_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:33.270917+00:00
-- url     : https://prove2.me/theorems/7fb5a716-e78e-44e5-8ff4-0f1ce823621a
-- title:
--   Theorem 1 — F(x, s, M) = F̂(x, s, M), realized by the finite-horizon Gittins index rule
-- statement:
--   Consider Whittle's bandit process: $N$ projects with measurable state spaces, Markov transition kernels $P_i$, measurable rewards bounded as $k(1-\beta) \le R_i(x_i) \le K(1-\beta)$, and discount $0 \le \beta < 1$, modified by the option to retire at any time for the reward $M$. Project $i$ may be operated at most $s_i$ more times. Let $F(x, s, M)$ be the maximal expected reward of this process, let $\varphi_i(x_i, s_i, M)$ be the corresponding value of the single-project process (14), and let $M_i(x_i, s_i)$ be the infimal $M$ for which $\varphi_i(x_i, s_i, M) = M$. Define
--   $$\hat F(x, s, M) = K - \int_M^K \prod_i \frac{\partial \varphi_i(x_i, s_i, m)}{\partial m}\, dm. \qquad (13)$$
--
--   **Theorem 1.** The maximal reward $F(x, s, M)$ equals $\hat F(x, s, M)$:
--   $$F(x, s, M) = \hat F(x, s, M).$$
--   It is realized by a policy in which at $(x, s)$ one engages a project $i$ maximizing $M_i(x_i, s_i)$ if this maximal value exceeds $M$, and otherwise retires.
--
--   The theorem reduces the $N$-project problem to $N$ single-project retirement problems, and shows that the Gittins index $v_i = (1-\beta)M_i$ rule is optimal; the infinite-horizon identity (12) follows by letting the horizons grow.
--
--   **Formalization Note** $F$ is the backward-induction value of $F = \max(M, \max_i L_iF)$ with $F(x, 0, M) = M$, the maximum running over projects with $s_i > 0$; it is not defined through $\hat F$ or the index. The statement has three parts: (1) $F = \hat F$; (2) every measurable index rule (with arbitrary tie-breaking among projects of maximal index) earns exactly $F$; (3) no feasible measurable Markov allocation policy earns more than $F$, which records the meaning of "maximal reward" for such policies and is the standard backward-induction fact rather than something the paper proves. The index of a project with $s_i = 0$ is the paper's $-\infty$: such projects are never engaged and do not enter the maximum. $\partial/\partial m$ is the right derivative; policies are required to have measurable decision sets so that their expected rewards are well defined. Projects are indexed by `Fin N`.
-- source:
--   Whittle, Multi-armed Bandits and the Gittins Index, J. R. Statist. Soc. B 42 (1980), p. 147 (PDF 5), Theorem 1

import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Theorem 1 (p. 147): the maximal reward `F(x, s, M)` equals `F̂(x, s, M)` of (13); it is
realized by every (measurable) index rule, which at `(x, s)` engages a project maximizing
`Mᵢ(xᵢ, sᵢ)` if this maximal value exceeds `M` and otherwise retires; and no feasible measurable
Markov allocation policy earns more than `F`. -/
theorem theorem1_index_rule {N : ℕ} {X : Fin N → Type*} [∀ i, MeasurableSpace (X i)]
    (B : BanditProcess N X) (x : ∀ j, X j) (s : Fin N → ℕ) (M : ℝ) :
    F B x s M = Fhat B x s M ∧
      (∀ σ : Policy N X, IsMeasurablePolicy σ → IsIndexRule B σ →
        polValue B σ x s M = F B x s M) ∧
      (∀ σ : Policy N X, IsFeasible σ → IsMeasurablePolicy σ →
        polValue B σ x s M ≤ F B x s M) := by sorry

end WhittleGittins.Retirement
