-- Prove2me | Theorems.Thm_ProjNewton_Superlinear_well_defined
-- name    : ProjNewton.Superlinear.well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:30:39.621726+00:00
-- url     : https://prove2.me/theorems/437b9702-268e-41b1-bd05-757258094c0d
-- title:
--   After (37) — finite line search, descent and critical-point termination
-- statement:
--   For the algorithm of (32)–(37) with $f\in C^1$, each feasible noncritical point has a sufficiently small trial step accepted by the Armijo inequality: some $m_0$ makes every $m\ge m_0$ acceptable. At a critical point, $m=0$ is accepted and the projected unit step fixes the point. Consequently every run with admissible matrices stays feasible, strictly decreases $f$ at a noncritical iterate, and remains fixed at a critical iterate.
--
--   $$x_k\text{ noncritical}\ \Longrightarrow\ f(x_{k+1})<f(x_k),\qquad x_k\text{ critical}\ \Longrightarrow\ x_{k+1}=x_k.$$
--
--   This records the well-definedness and descent conclusion stated after (37).
--
--   **Formalization Note** The run predicate chooses the first acceptable nonnegative exponent, as on p. 229. The fixed-point sentence on p. 230 says “for all $\alpha\ge0$,” matching Proposition 1(a).
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), pp. 229–230, §2 discussion after (37)

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear

open Matrix Filter Topology

/-- Bertsekas (1982), discussion following (37), pp. 229–230. -/
theorem well_defined {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf : ContDiff ℝ 1 f) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) :
    (∀ (x : Vec n), x ∈ orthant n →
      ∀ (D : Matrix (Fin n) (Fin n) ℝ), D.PosDef →
      DiagonalWrt D (Ik f μ ε x) →
      (¬ IsCritical f x → ∃ m₀ : ℕ, ∀ m ≥ m₀, Armijo f μ ε β σ D x m) ∧
      (IsCritical f x → Armijo f μ ε β σ D x 0 ∧ arc f D x 1 = x)) ∧
    (∀ (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n),
      IsRun f μ ε β σ D x → AdmissibleScaling f μ ε D x →
      ∀ k, x k ∈ orthant n ∧
        (¬ IsCritical f (x k) → f (x (k + 1)) < f (x k)) ∧
        (IsCritical f (x k) → x (k + 1) = x k)) := by sorry

end ProjNewton.Superlinear
