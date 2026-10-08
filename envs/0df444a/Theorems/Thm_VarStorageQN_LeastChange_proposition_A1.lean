-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_proposition_A1
-- name    : VarStorageQN.LeastChange.proposition_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:09.221752+00:00
-- url     : https://prove2.me/theorems/bb29e66e-cb29-4fc8-a909-8dc314df68c9
-- title:
--   Proposition A.1 — unique nonsymmetric least-change secant update
-- statement:
--   Let $B$ be any bounded operator on a real Hilbert space, let $R_1,R_2$ be bijective bounded operators, and let $s,y$ be vectors with $s\ne0$. Put $c=R_2^{-*}R_2^{-1}s$. Then
--
--   $$P_c=\frac{[y-Bs,c]}{\langle c,s\rangle}$$
--
--   belongs to $\Pi=\{P\in L_2(\mathcal H):(B+P)s=y\}$ and is the unique minimizer of $\|R_1PR_2\|_{\mathrm{HS}}$ over $P\in\Pi$. The formula is independent of $R_1$ and uses $R_2$ only through $c$.
--
--   This characterizes the rank-one weighted least-change update before self-adjointness is imposed.
--
--   **Formalization Note** The Hilbert space may have arbitrary dimension; each basis parameter is arbitrary. `R₁` and `R₂` are continuous linear equivalences, equivalent here to bijective bounded operators. The three clauses of unique solution are feasibility, minimality, and equality of every feasible minimizer with $P_c$. The denominator is nonzero because $s\ne0$ and $R_2$ is invertible; this is a consequence, not an added hypothesis.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 27, Proposition A.1 and (A.4)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket
import Definitions.Def_VarStorageQN_LeastChange_SecantProblem

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition A.1, p. 27: the unique minimizer of (A.4). -/
theorem proposition_A1 {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (R₁ R₂ : H ≃L[ℝ] H) (y s : H) (hs : s ≠ 0) :
    let c := weight R₂ s
    let Pc : H →L[ℝ] H := (⟪c, s⟫_ℝ)⁻¹ • bracket (y - B s) c
    let obj : (H →L[ℝ] H) → ℝ :=
      fun P => hsNorm b ((R₁ : H →L[ℝ] H) ∘L P ∘L (R₂ : H →L[ℝ] H))
    Pc ∈ Feas b B y s ∧
      (∀ P ∈ Feas b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ Feas b B y s, (∀ Q ∈ Feas b B y s, obj P ≤ obj Q) → P = Pc) := by sorry

end VarStorageQN.LeastChange
