-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_proposition_A2
-- name    : VarStorageQN.LeastChange.proposition_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:09.929581+00:00
-- url     : https://prove2.me/theorems/06f30b5e-6267-4759-864c-74e4b86c8dba
-- title:
--   Proposition A.2 — unique self-adjoint least-change secant update
-- statement:
--   Let $B$ be a self-adjoint bounded operator on a real Hilbert space, let $R$ be a bijective bounded operator, and let $s,y$ be vectors with $s\ne0$. Put $r=y-Bs$ and $c=R^{-*}R^{-1}s$. Then
--
--   $$P_c=\frac{[r,c]+[c,r]}{\langle c,s\rangle}
--   -\frac{\langle r,s\rangle}{\langle c,s\rangle^2}[c,c]$$
--
--   belongs to $\Pi_S=\{P\in L_2(\mathcal H):P=P^*,\ (B+P)s=y\}$ and is the unique minimizer of $\|R^*PR\|_{\mathrm{HS}}$ over $P\in\Pi_S$. The formula depends on $R$ only through $c$.
--
--   This is the symmetric weighted least-change characterization of the update (A.7).
--
--   **Formalization Note** The paper says “problem (A.5)” in Proposition A.2, but (A.5) is Broyden's displayed formula; its preceding paragraph defines the symmetric optimization problem as (A.6), which is the problem stated here. The Hilbert space and basis index type are arbitrary. A continuous linear equivalence represents the bijective operator. The denominator is nonzero as a consequence of $s\ne0$. Unique solution includes feasibility, minimality, and uniqueness among feasible minimizers.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 28, Proposition A.2, (A.6)–(A.7)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket
import Definitions.Def_VarStorageQN_LeastChange_SecantProblem

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition A.2, p. 28: the unique minimizer of (A.6), despite its (A.5) misprint. -/
theorem proposition_A2 {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (hB : IsSelfAdjoint B) (R : H ≃L[ℝ] H) (y s : H) (hs : s ≠ 0) :
    let c := weight R s
    let r := y - B s
    let Pc : H →L[ℝ] H :=
      (⟪c, s⟫_ℝ)⁻¹ • (bracket r c + bracket c r) -
        (⟪r, s⟫_ℝ / ⟪c, s⟫_ℝ ^ 2) • bracket c c
    let obj : (H →L[ℝ] H) → ℝ :=
      fun P => hsNorm b (adjoint (R : H →L[ℝ] H) ∘L P ∘L (R : H →L[ℝ] H))
    Pc ∈ FeasSym b B y s ∧
      (∀ P ∈ FeasSym b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ FeasSym b B y s, (∀ Q ∈ FeasSym b B y s, obj P ≤ obj Q) → P = Pc) := by sorry

end VarStorageQN.LeastChange
