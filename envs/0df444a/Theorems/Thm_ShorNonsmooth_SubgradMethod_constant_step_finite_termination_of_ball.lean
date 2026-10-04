-- Prove2me | Theorems.Thm_ShorNonsmooth_SubgradMethod_constant_step_finite_termination_of_ball
-- name    : ShorNonsmooth.SubgradMethod.constant_step_finite_termination_of_ball
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:02:14.227976+00:00
-- url     : https://prove2.me/theorems/63b7a17c-ff65-44e6-a83a-9784f5fe899f
-- title:
--   Theorem 2.1, Corollary 2 — if $M^*$ contains a ball of radius $r > h/2$, constant steps reach $M^*$
-- statement:
--   Let $f$ be a convex function on $E_n$ whose set $M^*$ of minimum points contains a closed ball of radius $r$ with
--   $$
--   r > \frac{h}{2} > 0 .
--   $$
--   Then for every starting point $x_0$ and every choice of subgradients, the method $x_{k+1} = x_k - h\, g_f(x_k)/\|g_f(x_k)\|$ produces, after finitely many steps, a point $x_{k^*} \in M^*$.
--
--   Finite termination of this kind is what makes the subgradient method exact for problems whose solution set has nonempty interior, such as systems of convex inequalities.
--
--   **Formalization Note** The book's "sphere" is a ball; the hypothesis is `Metric.closedBall c r ⊆ M*`. Because $M^*$ is closed, this is equivalent to the open ball being contained in $M^*$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 24, Corollary 2 (to Theorem 2.1)

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 24, Corollary 2 (of Theorem 2.1). If the set `M*` of minimum points of the
convex function `f` contains a ball (the book's "sphere") of radius `r` with `r > h/2 > 0`, and the
subgradient method is applied with `h_{k+1}(x_k) = h / ‖g_f(x_k)‖`, then some iterate `x_{k*}`
lies in `M*` (for every subgradient selection and every start `x₀`). -/
theorem constant_step_finite_termination_of_ball {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (c : EuclideanSpace ℝ (Fin n)) (r h : ℝ)
    (hh : 0 < h / 2) (hr : h / 2 < r) (hball : Metric.closedBall c r ⊆ MinSet f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ kstar : ℕ, normalizedIter g (fun _ => h) x₀ kstar ∈ MinSet f := by sorry

end ShorNonsmooth.SubgradMethod
