-- Prove2me | Theorems.Thm_ProjNewton_Superlinear_proposition3
-- name    : ProjNewton.Superlinear.proposition3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:31:04.743156+00:00
-- url     : https://prove2.me/theorems/b5719594-b827-4e0e-8f28-68db437bf58f
-- title:
--   Proposition 3 — local attraction and finite binding-set identification
-- statement:
--   Let $x^*$ be a feasible local minimum satisfying Assumption (C). In addition to the bounds (41), assume each diagonal entry of $D_k$ indexed by $I_k^+$ is bounded below by a fixed positive number as in (65). There is a radius $\bar\delta>0$, chosen from these fixed data before choosing a run, such that any run entering the closed ball $\|x_{\bar k}-x^*\|\le\bar\delta$ converges to $x^*$ and, for all $k\ge\bar k+1$,
--
--   $$I_k^+=B(x_k)=B(x^*).$$
--
--   Thus the method identifies the binding coordinates after a finite number of iterations once it enters the attraction region.
--
--   **Formalization Note** Assumption (C) includes local $C^2$ smoothness, positive Hessian bounds on directions vanishing at $B(x^*)$, and strict complementarity on $B(x^*)$. The theorem does not assume (A). The run's admissible matrix condition, parameter ranges, $n\ge1$ and standing $C^1$ hypothesis are explicit.
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), p. 234, Proposition 3, (65)–(67); Assumption (C), p. 233

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear

open Matrix Filter Topology

/-- Bertsekas (1982), Proposition 3, p. 234. -/
theorem proposition3 {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf : ContDiff ℝ 1 f) (xs : Vec n)
    (hxs : xs ∈ orthant n) (hmin : IsLocalMinOn f (orthant n) xs)
    (hC : AssumptionC f xs) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (lam1 lam2 lambar : ℝ)
    (q₁ q₂ : ℕ) (hlambar : 0 < lambar) :
    ∃ deltabar : ℝ, 0 < deltabar ∧
      ∀ (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n),
        IsRun f μ ε β σ D x → AdmissibleScaling f μ ε D x →
        AssumptionB f μ D x lam1 lam2 q₁ q₂ →
        (∀ k, ∀ i ∈ Ik f μ ε (x k), lambar ≤ D k i i) →
        ∀ kbar, ‖x kbar - xs‖ ≤ deltabar →
          Tendsto x atTop (𝓝 xs) ∧
          ∀ k ≥ kbar + 1, Ik f μ ε (x k) = B (x k) ∧ B (x k) = B xs := by sorry

end ProjNewton.Superlinear
