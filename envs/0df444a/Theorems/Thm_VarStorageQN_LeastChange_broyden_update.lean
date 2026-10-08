-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_broyden_update
-- name    : VarStorageQN.LeastChange.broyden_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:10.728766+00:00
-- url     : https://prove2.me/theorems/5a1d8a1e-35e2-4124-b681-e1a2387a6a00
-- title:
--   (A.5) — Broyden's update solves (A.4) with R₂ = I
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $B$ a bounded operator on $\mathcal H$, $R_1$ a bijective bounded operator, and $y,s\in\mathcal H$ with $s\ne0$. Let $\Pi=\{P\in L_2(\mathcal H):(B+P)s=y\}$ be the Hilbert–Schmidt perturbations satisfying the secant equation. Then the problem
--
--   $$\min_{P\in\Pi}\ \|R_1P\|_{\mathrm{HS}}$$
--
--   (problem (A.4) with $R_2=I$) has the unique solution $P=[y-Bs,s]/|s|^2$, so the updated operator is Broyden's formula
--
--   $$B_{\mathrm{Broyden}}=B+\frac{[y-Bs,s]}{|s|^2}.$$
--
--   This is the instance $R_2=I$ of Proposition A.1, where $c=s$; it shows that Broyden's update is the least-change secant update for every left weight $R_1$.
--
--   **Formalization Note** "Unique solution" is stated as three clauses: $P_c\in\Pi$, $\|R_1P_c\|_{\mathrm{HS}}\le\|R_1P\|_{\mathrm{HS}}$ for all $P\in\Pi$, and every minimizer in $\Pi$ equals $P_c$. With $R_2=I$ the objective $R_1PR_2$ is written $R_1P$. $R_1$ is a continuous linear equivalence (a bounded bijection has a bounded inverse). The Hilbert–Schmidt norm is computed in an arbitrary Hilbert basis $b$ and summability is part of $\Pi$.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 28, Annex, (A.5)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket
import Definitions.Def_VarStorageQN_LeastChange_SecantProblem

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- (A.5), p. 28: with `R₂ = I`, the unique solution of (A.4) is Broyden's perturbation
`[y − Bs, s] / |s|²`, for every bijective `R₁`. -/
theorem broyden_update {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (R₁ : H ≃L[ℝ] H) (y s : H) (hs : s ≠ 0) :
    let Pc : H →L[ℝ] H := (‖s‖ ^ 2)⁻¹ • bracket (y - B s) s
    let obj : (H →L[ℝ] H) → ℝ := fun P => hsNorm b ((R₁ : H →L[ℝ] H) ∘L P)
    Pc ∈ Feas b B y s ∧
      (∀ P ∈ Feas b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ Feas b B y s, (∀ Q ∈ Feas b B y s, obj P ≤ obj Q) → P = Pc) := by sorry

end VarStorageQN.LeastChange
