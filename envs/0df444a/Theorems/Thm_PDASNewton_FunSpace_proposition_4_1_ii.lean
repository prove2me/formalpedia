-- Prove2me | Theorems.Thm_PDASNewton_FunSpace_proposition_4_1_ii
-- name    : PDASNewton.FunSpace.proposition_4_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:55.842721+00:00
-- url     : https://prove2.me/theorems/0c9c56d6-4213-4ca0-a102-968fdc8abfa0
-- title:
--   Proposition 4.1(ii), p. 11 — max(0,·): L^q → L^p, 1 ≤ p < q ≤ ∞, is slantly differentiable with slanting function G_m
-- statement:
--   Let $(\Omega, \mu)$ be a finite measure space, $1 \le p < q \le \infty$ and $\delta \in \mathbb{R}$, and let $G_m$ be the function (4.1) with this $\delta$. Then for every $y \in L^q(\Omega)$ and every $\varepsilon > 0$ there is $\eta > 0$ such that every $h \in L^q(\Omega)$ with $\|h\|_{L^q} < \eta$ satisfies
--   $$\big\|\max(0, y+h) - \max(0, y) - G_m(y+h)\,h\big\|_{L^p} \le \varepsilon\,\|h\|_{L^q}.$$
--   That is, $\max(0, \cdot) : L^q(\Omega) \to L^p(\Omega)$ is slantly differentiable on $L^q(\Omega)$ and $G_m$ is a slanting function.
--
--   The gap $p < q$ between the two norms is what makes the pointwise max slantly differentiable in function space; Proposition 4.1(i) shows that it cannot be removed.
--
--   **Formalization Note** The paper's bounded domain with Lipschitz boundary is replaced by an arbitrary finite measure space (the proof uses only $|\Omega| < \infty$). The slanting function is written as the pointwise multiplication $h \mapsto G_m(y+h)h$, without packaging it as an element of $\mathcal{L}(L^q, L^p)$.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 11, Proposition 4.1(ii); proof in Appendix A, pp. 21–22

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

namespace PDASNewton.FunSpace

open MeasureTheory
open scoped ENNReal

/-- Proposition 4.1(ii), p. 11: for `1 ≤ p < q ≤ ∞` on a finite measure space, `max(0, ·)` is
slantly differentiable from `L^q` to `L^p` with slanting function `G_m` of (4.1), for every `δ`:
property (A) holds at every `y ∈ L^q`. -/
theorem proposition_4_1_ii {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p < q) (δ : ℝ) :
    ∀ y : α → ℝ, MemLp y q μ → MaxSlantingAt μ p q δ y := by sorry

end PDASNewton.FunSpace
