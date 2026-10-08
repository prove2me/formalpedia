-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_theorem_5_7
-- name    : SelfScaledIPM.FuncProx.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:32.194377+00:00
-- url     : https://prove2.me/theorems/4ae4f89d-06b8-4d68-b473-9f17bef3ea3b
-- title:
--   Theorem 5.7, p. 25 — one Newton centering step lowers γ_F by at least τ − ln(1 + τ), τ = (γ_G/(1 + γ_∞))^{1/2} ≥ γ_∞/(1 + γ_∞)
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, $A$ surjective, $(x,y,s)$ strictly feasible, and let $(x',y',s')$ be obtained from it by one step of the Newton process (5.25)–(5.26). Then $(x',y',s')$ is strictly feasible and
--   $$\gamma_F(x',s')\le\gamma_F(x,s)-[\tau-\ln(1+\tau)], \tag{5.27}$$
--   where
--   $$\tau=\Big(\frac{\gamma_G(x,s)}{1+\gamma_\infty(x,s)}\Big)^{1/2}\ge\frac{\gamma_\infty(x,s)}{1+\gamma_\infty(x,s)} .$$
--
--   Applied at every iterate, this is the paper's "for any $k\ge0$": the Newton process decreases the functional proximity measure by a definite amount as long as the point is away from the central path, which bounds the number of corrector steps in Algorithm 7.1.
--
--   **Formalization Note** The statement is for one step; the paper's "for any $k\ge0$" is the same claim at each iterate. Strict feasibility of the new point is implicit on the page (the process is run indefinitely and $\gamma_F$ is evaluated at every iterate) and is stated as a conclusion.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 25, Theorem 5.7, (5.25)–(5.27)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Definitions.Def_SelfScaledIPM_FuncProx_Directions

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Theorem 5.7** (p. 25), one step of the Newton process (5.25)–(5.26). If `(x, y, s)` is
strictly feasible and `(x', y', s')` is obtained from it by one Newton step, then `(x', y', s')` is
strictly feasible and (5.27) `γ_F(x', s') ≤ γ_F(x, s) − [τ − ln(1 + τ)]`, where
`τ = (γ_G(x, s)/(1 + γ_∞(x, s)))^{1/2} ≥ γ_∞(x, s)/(1 + γ_∞(x, s))`. -/
theorem theorem_5_7
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hfeas : IsStrictlyFeasible K A b c x y s)
    (x' : EuclideanSpace ℝ (Fin n)) (y' : EuclideanSpace ℝ (Fin m)) (s' : EuclideanSpace ℝ (Fin n))
    (hstep : IsNewtonStep K F ν A (x, y, s) (x', y', s')) :
    IsStrictlyFeasible K A b c x' y' s' ∧
    gammaF K F ν x' s' ≤ gammaF K F ν x s -
      (Real.sqrt (gammaG K F ν x s / (1 + gammaInf K F ν x s)) -
        Real.log (1 + Real.sqrt (gammaG K F ν x s / (1 + gammaInf K F ν x s)))) ∧
    gammaInf K F ν x s / (1 + gammaInf K F ν x s) ≤
      Real.sqrt (gammaG K F ν x s / (1 + gammaInf K F ν x s)) := by sorry

end SelfScaledIPM.FuncProx
