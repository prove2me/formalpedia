-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_psb_update
-- name    : VarStorageQN.LeastChange.psb_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:41.904822+00:00
-- url     : https://prove2.me/theorems/1162708d-6470-444f-b7c6-cd398fef3176
-- title:
--   Annex p. 29 — the psb update solves (A.6) with R = I
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $B=B^*$ a self-adjoint bounded operator, and $y,s\in\mathcal H$ with $s\ne0$; put $r=y-Bs$. Let $\Pi_S=\{P\in L_2(\mathcal H):P=P^*,\ (B+P)s=y\}$. Then $\min_{P\in\Pi_S}\|P\|_{\mathrm{HS}}$ (problem (A.6) with $R=I$) has the unique solution
--
--   $$P=\frac{[r,s]+[s,r]}{|s|^2}-\frac{\langle r,s\rangle}{|s|^4}[s,s],$$
--
--   so the updated operator is the Powell symmetric Broyden (psb) formula $B_{\mathrm{psb}}=B+P$.
--
--   This is the instance $R=I$ (so $c=s$) of Proposition A.2.
--
--   **Formalization Note** The paper writes "If we take $R=I$ in problem (A.5)"; (A.5) is Broyden's formula and the minimization problem with weight $R$ is (A.6), so we state (A.6), as for Proposition A.2. "Unique solution" is feasibility, minimality and equality of every feasible minimizer with $P$. The Hilbert–Schmidt norm uses an arbitrary Hilbert basis; summability is part of $\Pi_S$.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 29, Annex, psb update formula (after Proposition A.2)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket
import Definitions.Def_VarStorageQN_LeastChange_SecantProblem

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- p. 29: with `R = I`, the unique solution of (A.6) (printed "(A.5)") is the psb perturbation. -/
theorem psb_update {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (hB : IsSelfAdjoint B) (y s : H) (hs : s ≠ 0) :
    let r := y - B s
    let Pc : H →L[ℝ] H :=
      (‖s‖ ^ 2)⁻¹ • (bracket r s + bracket s r) - (⟪r, s⟫_ℝ / ‖s‖ ^ 4) • bracket s s
    let obj : (H →L[ℝ] H) → ℝ := fun P => hsNorm b P
    Pc ∈ FeasSym b B y s ∧
      (∀ P ∈ FeasSym b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ FeasSym b B y s, (∀ Q ∈ FeasSym b B y s, obj P ≤ obj Q) → P = Pc) := by sorry

end VarStorageQN.LeastChange
