-- Prove2me | Theorems.Thm_RobbinsMonroSA_Conv_eq_42
-- name    : RobbinsMonroSA.Conv.eq_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:13:21.03517+00:00
-- url     : https://prove2.me/theorems/0ea68b0b-50a6-47e5-9a66-08c335eed690
-- title:
--   (36)–(42), pp. 404–405 — under (33)–(35), (M(x) − α)/(x − θ) ≥ δM′(θ)/2A_n for 0 < |x − θ| ≤ A_n
-- statement:
--   Let $M : \mathbb R \to \mathbb R$ be nondecreasing (33), with $M(\theta) = \alpha$ (34) and with derivative $M'(\theta) > 0$ at $\theta$ (35). Then there is a constant $\delta > 0$ such that for every $A$ with $\delta/A \le 1$,
--   $$\frac{M(x) - \alpha}{x - \theta} \ge \frac{\delta M'(\theta)}{2A} \qquad\text{for } 0 < |x - \theta| \le A. \tag{42}$$
--
--   Applied with $A = A_n$ (which tends to infinity), this gives (25) with $K = \delta M'(\theta)/2 > 0$, so Lemma 2 applies under (33)–(35).
--
--   **Formalization Note** This is a deterministic statement about any function $M$. The paper's "we may assume without loss of generality that $\delta/A_n \le 1$" is the hypothesis $\delta \le A$; differentiability at $\theta$ is `HasDerivAt M M' θ`.
-- source:
--   Robbins and Monro, A stochastic approximation method, Ann. Math. Statist. 22 (1951), pp. 404–405, (33)–(42)

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsMonroSA.Conv

/-- (36)–(42), pp. 404–405. If `M` is nondecreasing with `M(θ) = α` and `M′(θ) > 0`, there is
`δ > 0` such that for every `A ≥ δ`, `(M(z) - α)/(z - θ) ≥ δ M′(θ) / 2A` on `0 < |z - θ| ≤ A`. -/
theorem eq_42 (M : ℝ → ℝ) (α θ M' : ℝ) (h33 : Monotone M) (h34 : M θ = α)
    (h35 : HasDerivAt M M' θ) (h35pos : 0 < M') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, δ ≤ A → ∀ z : ℝ, 0 < |z - θ| → |z - θ| ≤ A →
      δ * M' / (2 * A) ≤ (M z - α) / (z - θ) := by sorry

end RobbinsMonroSA.Conv
