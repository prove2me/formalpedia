-- Prove2me | Theorems.Thm_RobinsonSR_Schur_strongly_monotone_inverse_lipschitz
-- name    : RobinsonSR.Schur.strongly_monotone_inverse_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:19.420896+00:00
-- url     : https://prove2.me/theorems/a2abc45c-51e3-40b6-82f0-dfb971a22f06
-- title:
--   The positive definite reduced operator has a global Lipschitz inverse
-- statement:
--   Let $K\subseteq\mathbb R^s$ be nonempty, closed, and convex. If $A_{11}$ is nonsingular and its Schur complement $M=A/A_{11}$ satisfies $w^\top Mw>0$ for every nonzero $w$, without assuming symmetry, then $S(w)=Mw+N_K(w)$ has a unique inverse value at every $z\in\mathbb R^s$, and one constant $L$ satisfies
--
--   $$
--   \|S^{-1}(z_1)-S^{-1}(z_2)\|\leq L\|z_1-z_2\|.
--   $$
--
--   This gives the global reduced inverse used in the sufficient direction of Theorem 3.1.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 52, first paragraph of proof of Theorem 3.1

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 52, the inverse of the reduced operator. -/
theorem strongly_monotone_inverse_lipschitz (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0)
    (K : Set (EuclideanSpace ℝ (Fin s)))
    (hK₁ : K.Nonempty) (hK₂ : IsClosed K) (hK₃ : Convex ℝ K)
    (hM : PosDefNS (schur A₁₁ A₁₂ A₂₁ A₂₂)) :
    InvIsLipschitzFunction (schur A₁₁ A₁₂ A₂₁ A₂₂) K := by sorry

end RobinsonSR.Schur
