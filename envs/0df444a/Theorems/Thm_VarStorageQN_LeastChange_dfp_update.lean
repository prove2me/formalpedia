-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_dfp_update
-- name    : VarStorageQN.LeastChange.dfp_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:18.715963+00:00
-- url     : https://prove2.me/theorems/f42691e8-f3c5-4451-832d-53fbb124c64b
-- title:
--   (A.8) — with R = C⁻¹, c = y and (A.7) is the dfp update
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $B=B^*$ a self-adjoint bounded operator, and $y,s\in\mathcal H$ with $\langle y,s\rangle>0$. Let $C$ be a bijective bounded operator with $y=C^*Cs$ (one exists by Proposition A.3) and take $R=C^{-1}$. Then the weight vector is $c=R^{-*}R^{-1}s=y$, and the unique solution of
--
--   $$\min_{P\in\Pi_S}\|R^*PR\|_{\mathrm{HS}},\qquad \Pi_S=\{P\in L_2(\mathcal H):P=P^*,\ (B+P)s=y\},$$
--
--   is $P=B_{\mathrm{dfp}}-B$, where
--
--   $$B_{\mathrm{dfp}}=B+\frac{[y-Bs,y]+[y,y-Bs]}{\langle y,s\rangle}-\frac{\langle y-Bs,s\rangle}{\langle y,s\rangle^2}[y,y].\tag{A.8}$$
--
--   So the Davidon–Fletcher–Powell update is a weighted least-change self-adjoint secant update.
--
--   **Formalization Note** Both conjuncts of the paper's sentence are stated: $c=y$, and the unique-solution property (feasibility, minimality, equality of every feasible minimizer) of $B_{\mathrm{dfp}}-B$ for (A.6) with $R=C^{-1}$. $C$ is a continuous linear equivalence and $R$ is its inverse `C.symm`. The Hilbert–Schmidt norm uses an arbitrary Hilbert basis; summability is part of $\Pi_S$.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), pp. 29–30, Annex, sentence before (A.8) and (A.8)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket
import Definitions.Def_VarStorageQN_LeastChange_SecantProblem

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- (A.8), pp. 29–30: if `⟨y,s⟩ > 0` and `y = C*Cs` with `C` bijective, then for `R = C⁻¹`
the weight is `c = y`, and the unique solution of (A.6) is the dfp perturbation `B_dfp − B`. -/
theorem dfp_update {ι : Type*} (b : HilbertBasis ι ℝ H) (B : H →L[ℝ] H)
    (hB : IsSelfAdjoint B) (y s : H) (hys : 0 < ⟪y, s⟫_ℝ) (C : H ≃L[ℝ] H)
    (hC : y = adjoint (C : H →L[ℝ] H) (C s)) :
    let R : H ≃L[ℝ] H := C.symm
    let r := y - B s
    let Pc : H →L[ℝ] H :=
      (⟪y, s⟫_ℝ)⁻¹ • (bracket r y + bracket y r) - (⟪r, s⟫_ℝ / ⟪y, s⟫_ℝ ^ 2) • bracket y y
    let obj : (H →L[ℝ] H) → ℝ :=
      fun P => hsNorm b (adjoint (R : H →L[ℝ] H) ∘L P ∘L (R : H →L[ℝ] H))
    weight R s = y ∧
      Pc ∈ FeasSym b B y s ∧
      (∀ P ∈ FeasSym b B y s, obj Pc ≤ obj P) ∧
      (∀ P ∈ FeasSym b B y s, (∀ Q ∈ FeasSym b B y s, obj P ≤ obj Q) → P = Pc) := by sorry

end VarStorageQN.LeastChange
