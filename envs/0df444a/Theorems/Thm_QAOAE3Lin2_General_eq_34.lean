-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_34
-- name    : QAOAE3Lin2.General.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:43.546313+00:00
-- url     : https://prove2.me/theorems/99ddc6c0-41a7-4b42-9db0-06a9d57af25b
-- title:
--   Section II, (33)–(34), p. 7 — |R^k(γ)| ≤ (9D^{1/2}|γ|)^{k+2} for odd k and D ≥ 1
-- statement:
--   Let an instance of Max E3LIN2 have every equation on three distinct bits, no triple carrying two equations, and every bit in at most $D+1$ equations, with $D\ge1$. Let $k$ be odd. For every equation and every real $\gamma$, the remainder $R^k$ of (26) satisfies
--   $$|R^k(\gamma)|\le\big(9D^{1/2}|\gamma|\big)^{k+2}.$$
--
--   It is the uniform, instance-free remainder bound: for $|\gamma|\le1/(10D^{1/2})$ each clause contributes at most $(9/10)^{k+2}$.
--
--   **Formalization Note.** $D\ge1$ is added. The page's last step uses $e(1+9D)^{1/2}\le 9D^{1/2}$, which holds for $D\ge1$ and fails at $D=0$. The page's justification "$e<3$" does not give this step on its own, since $3(1+9D)^{1/2}>9D^{1/2}$; the stated inequality is still true for $D\ge1$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 7, Section II, (33)–(34)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_34 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (hD : 1 ≤ D)
    (k : ℕ) (hk : Odd k) (i : Fin m) (γ : ℝ) :
    |Rk tri rhs i k γ| ≤ (9 * Real.sqrt D * |γ|) ^ (k + 2) := by sorry

end QAOAE3Lin2.General
