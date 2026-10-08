-- Prove2me | Theorems.Thm_SAARate_Sharp_sharp_iff_dirDeriv_pos
-- name    : SAARate.Sharp.sharp_iff_dirDeriv_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:00.256847+00:00
-- url     : https://prove2.me/theorems/d3f808ce-0800-4d89-a546-2bb58e1abb33
-- title:
--   (2.3), p. 4 — for a convex problem, a sharp unique minimum at x̄ iff g′(x̄, d) > 0 on T_Θ(x̄) \ {0}
-- statement:
--   Let $g:\mathbb R^m\to\mathbb R$ be convex, let $\Theta\subseteq\mathbb R^m$ be convex and let $\bar x\in\Theta$. Write $g'(\bar x,d)$ for the directional derivative of $g$ at $\bar x$ in the direction $d$, and $T_\Theta(\bar x)$ for the tangent cone to $\Theta$ at $\bar x$. Then the following are equivalent:
--
--   1. $\bar x$ is the unique minimizer of $g$ over $\Theta$, and there is $c>0$ with $g(x)\ge g(\bar x)+c\|x-\bar x\|$ for all $x\in\Theta$ (a **sharp minimum**);
--   2. the directional derivative is positive on all nonzero tangent directions:
--   $$
--   g'(\bar x,d)>0\qquad\forall\, d\in T_\Theta(\bar x)\setminus\{0\}.
--   $$
--
--   For $g=f$ this is the paper's statement that Assumption (A) holds iff (2.3). It is used twice in the proof of Theorem 2.1: at the true problem, to turn (A) into a condition on $f'(\bar x,\cdot)$, and at the approximating problem, to turn positivity of $\hat f'_N(\bar x,\cdot)$ into a sharp, hence unique, minimum at $\bar x$.
--
--   **Formalization Note.** The statement is made for an arbitrary finite convex function $g$, not only for the expected value function $f$; this is stronger than the page and covers both uses. The tangent cone is Mathlib's `posTangentConeAt Θ x̄`, the set of limits of $c_n d_n$ with $c_n\ge 0$, $d_n\to0$ and $\bar x+d_n\in\Theta$; for convex $\Theta$ this is the closure of $\mathbb R_+(\Theta-\bar x)$, the tangent cone of convex analysis that the paper uses. (Mathlib's `tangentConeAt ℝ`, which allows negative $c_n$, is a different, symmetric cone and is not used.) Closedness of $\Theta$ is not needed and not assumed.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 4, Assumption (A), (2.2), (2.3)

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem sharp_iff_dirDeriv_pos {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (Θ : Set (E m)) (hΘ : Convex ℝ Θ) (xbar : E m) (hx : xbar ∈ Θ) :
    (argminOn g Θ = {xbar} ∧ ∃ c > 0, ∀ x ∈ Θ, g x ≥ g xbar + c * ‖x - xbar‖) ↔
      ∀ d ∈ posTangentConeAt Θ xbar, d ≠ 0 → 0 < dirDeriv g xbar d := by sorry

end SAARate.Sharp
