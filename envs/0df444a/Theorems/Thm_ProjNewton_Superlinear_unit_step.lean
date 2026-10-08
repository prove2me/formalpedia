-- Prove2me | Theorems.Thm_ProjNewton_Superlinear_unit_step
-- name    : ProjNewton.Superlinear.unit_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:31:17.860905+00:00
-- url     : https://prove2.me/theorems/f6b449ad-0339-419a-b238-6c6ed79bc251
-- title:
--   After Proposition 4 — eventual acceptance of the unit step
-- statement:
--   Use the convex $C^2$ problem, unique feasible optimum, Assumption (C), level-set Hessian bounds and matrix choice $D_k=H_k^{-1}$ of Proposition 4. For the resulting first-acceptable-step run, the initial trial $a=1$ satisfies (37) for all sufficiently large $k$:
--
--   $$\exists K\ \forall k\ge K:\quad f(x_k)-f(x_k(1))\ge\sigma\operatorname{RHS}_{37}(1).$$
--
--   Hence the Armijo search eventually accepts the unity stepsize at its first trial.
--
--   **Formalization Note** The printed Hessian-bound quantifier in Proposition 4 is read as “every point $y$ in the unrestricted initial level set and every direction $z$.” The first-trial exponent is $m=0$; $D_k$ is constructed from $H_k$, with no invertibility or matrix admissibility premise.
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), p. 236, §2 after Proposition 4

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear

open Matrix Filter Topology

/-- Bertsekas (1982), after Proposition 4, p. 236. -/
theorem unit_step {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (xs : Vec n) (hopt : xs ∈ orthant n ∧ ∀ y ∈ orthant n, f xs ≤ f y)
    (huniq : ∀ y ∈ orthant n, (∀ z ∈ orthant n, f y ≤ f z) → y = xs)
    (hC : AssumptionC f xs) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : ℕ → Vec n)
    (hm : ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧
      ∀ y : Vec n, f y ≤ f (x 0) → ∀ z : Fin n → ℝ,
        m₁ * (z ⬝ᵥ z) ≤ hessForm f y z ∧ hessForm f y z ≤ m₂ * (z ⬝ᵥ z))
    (hrun : IsRun f μ ε β σ (fun k => (Hmat f μ ε (x k))⁻¹) x) :
    ∀ᶠ k in atTop, Armijo f μ ε β σ ((Hmat f μ ε (x k))⁻¹) (x k) 0 := by sorry

end ProjNewton.Superlinear
