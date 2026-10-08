-- Prove2me | Theorems.Thm_RobinsonSR_Schur_theorem_3_1
-- name    : RobinsonSR.Schur.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:08.578281+00:00
-- url     : https://prove2.me/theorems/ae8570b2-8559-4bf0-9be0-a4ea837735f5
-- title:
--   Theorem 3.1 — Schur-complement sufficient condition and P-matrix characterization
-- statement:
--   Let $r,s$ be positive integers, let $K\subseteq\mathbb R^s$ be nonempty, closed, and convex, and partition $A$ into $r\times r$, $r\times s$, $s\times r$, and $s\times s$ blocks. Define $T_K(w)=Aw+N_{\mathbb R^r\times K}(w)$. If $A_{11}$ is nonsingular and its Schur complement $A/A_{11}$ is positive definite in the sense $v^\top(A/A_{11})v>0$ for nonzero $v$, then $T_K^{-1}$ is an everywhere-defined, single-valued, globally Lipschitz function. In the special case $K=\mathbb R^s_+$, this has an exact characterization:
--
--   $$
--   T_{\mathbb R^s_+}^{-1}\text{ is everywhere defined, unique and Lipschitz}
--   \quad\Longleftrightarrow\quad
--   \det A_{11}\ne0\ \text{and}\ A/A_{11}\text{ has positive principal minors}.
--   $$
--
--   The first assertion covers arbitrary nonempty closed convex $K$; the second replaces positive definiteness by the P-matrix condition on the orthant and asserts its necessity. Together these are Robinson's Theorem 3.1.
--
--   **Formalization Note** The Schur complement is only used under the nonsingularity condition; positive definiteness does not require a symmetric matrix. The Lean statement quantifies over all eligible $K$ for the first assertion and uses the orthant for the second.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 51, Theorem 3.1; proof pp. 51–52

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, Theorem 3.1, p. 51. -/
theorem theorem_3_1 (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) :
    (∀ K : Set (EuclideanSpace ℝ (Fin s)), K.Nonempty → IsClosed K → Convex ℝ K →
      A₁₁.det ≠ 0 → PosDefNS (schur A₁₁ A₁₂ A₂₁ A₂₂) →
      InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (prodSet K)) ∧
    (InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
        (prodSet (nonnegOrthant s)) ↔
      A₁₁.det ≠ 0 ∧ IsPMatrix (schur A₁₁ A₁₂ A₂₁ A₂₂)) := by sorry

end RobinsonSR.Schur
