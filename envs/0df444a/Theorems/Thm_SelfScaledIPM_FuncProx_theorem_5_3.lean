-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_theorem_5_3
-- name    : SelfScaledIPM.FuncProx.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:57.134418+00:00
-- url     : https://prove2.me/theorems/8dfc11ed-984b-4e60-a047-83caec8bb081
-- title:
--   Theorem 5.3, p. 22 — along the affine-scaling direction γ_F changes by F(x − αp_x) + F(x + α/(1−α) p_x) − 2F(x) = F(x + α²/(1−α) p(x,s)) − F(x)
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, $A$ surjective, $(x,y,s)$ strictly feasible with scaling point $w$ ($F''(w)x=s$), and $(p_x,p_y,p_s)$ the affine-scaling direction. Put $x(\alpha)=x-\alpha p_x$, $y(\alpha)=y-\alpha p_y$, $s(\alpha)=s-\alpha p_s$ and
--   $$p(x,s)=-\tfrac12[F''(x)]^{-1}F'''(x)\big[p_x,[F''(w)]^{-1}p_s\big].$$
--   Then:
--
--   1. for all sufficiently small $\alpha\ge0$ the point $(x(\alpha),y(\alpha),s(\alpha))$ is strictly feasible;
--   2. for every $\alpha\ge0$ for which it is strictly feasible, $\alpha<1$, the points $x+\frac{\alpha}{1-\alpha}p_x$ and $x+\frac{\alpha^2}{1-\alpha}p(x,s)$ lie in $\operatorname{int}K$, and
--   $$\gamma_F(x(\alpha),s(\alpha))-\gamma_F(x,s)=F(x-\alpha p_x)+F\Big(x+\frac{\alpha}{1-\alpha}p_x\Big)-2F(x)=F\Big(x+\frac{\alpha^2}{1-\alpha}p(x,s)\Big)-F(x). \tag{5.8}$$
--
--   The theorem reduces the predictor step of Algorithm 7.1 to the behaviour of $F$ along the single direction $p(x,s)$, with the step length entering only through $\xi=\alpha^2/(1-\alpha)$.
--
--   **Formalization Note** The vectors $[F''(w)]^{-1}p_s$ and $p(x,s)$ are given by their defining equations $F''(w)z=p_s$ and $F''(x)p=-\tfrac12F'''(x)[p_x,z]$. "For any such $\alpha$" is read as every $\alpha\ge0$ with $(x(\alpha),y(\alpha),s(\alpha))$ strictly feasible. The facts $\alpha<1$ and the two interior memberships are proved on the page ((5.9), (5.11), Theorem 3.11) and are stated as conclusions so that both sides of (5.8) are evaluated inside the barrier's domain.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 22, Theorem 5.3, (5.8); p. 23, definition of p(x, s)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Definitions.Def_SelfScaledIPM_FuncProx_Directions

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Theorem 5.3** (p. 22). Let `(x, y, s)` be strictly feasible with scaling point `w` and
affine-scaling direction `(p_x, p_y, p_s)`; let `z = [F''(w)]⁻¹p_s` and
`p = −½[F''(x)]⁻¹F'''(x)[p_x, z]` (given by `F''(w) z = p_s`, `F''(x) p = −½ F'''(x)[p_x, z]`).
(a) For small enough `α ≥ 0`, `(x − αp_x, y − αp_y, s − αp_s)` is strictly feasible.
(b) For every `α ≥ 0` for which it is strictly feasible: `α < 1`, the points `x + (α/(1−α))p_x`
and `x + (α²/(1−α))p` lie in `int K`, and (5.8)
`γ_F(x − αp_x, s − αp_s) − γ_F(x, s) = F(x − αp_x) + F(x + (α/(1−α))p_x) − 2F(x)
 = F(x + (α²/(1−α))p) − F(x)`. -/
theorem theorem_5_3
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hfeas : IsStrictlyFeasible K A b c x y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w)
    (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m)) (ps : EuclideanSpace ℝ (Fin n))
    (hp : IsAffineScalingDir A F s w px py ps)
    (z p : EuclideanSpace ℝ (Fin n)) (hz : SelfScaledIPM.ShortStep.hess F w z = ps) (hpdef : SelfScaledIPM.ShortStep.hess F x p = -(1 / 2 : ℝ) • third F x px z) :
    (∃ ε > 0, ∀ α ∈ Set.Ico (0 : ℝ) ε,
      IsStrictlyFeasible K A b c (x - α • px) (y - α • py) (s - α • ps)) ∧
    (∀ α : ℝ, 0 ≤ α → IsStrictlyFeasible K A b c (x - α • px) (y - α • py) (s - α • ps) →
      α < 1 ∧ x + (α / (1 - α)) • px ∈ interior K ∧ x + (α ^ 2 / (1 - α)) • p ∈ interior K ∧
      gammaF K F ν (x - α • px) (s - α • ps) - gammaF K F ν x s =
        F (x - α • px) + F (x + (α / (1 - α)) • px) - 2 * F x ∧
      F (x - α • px) + F (x + (α / (1 - α)) • px) - 2 * F x =
        F (x + (α ^ 2 / (1 - α)) • p) - F x) := by sorry

end SelfScaledIPM.FuncProx
