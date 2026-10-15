-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_31
-- name    : QAOAE3Lin2.General.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:25.733156+00:00
-- url     : https://prove2.me/theorems/9ce3ab42-d2f6-4d93-b391-fdfcb4c01163
-- title:
--   Section II, (31), p. 7 — E_z[c_i²] = Σ d_iab d_iab ≤ D
-- statement:
--   Let an instance of Max E3LIN2 have every equation on three distinct bits, no triple carrying two equations, and every bit in at most $D+1$ equations. Fix an equation and one of its bits, and let $c$ be the corresponding polynomial (21) with $D_c$ terms. Then
--   $$E_z[c^2]=\sum_{a<b}d_{iab}d_{iab}=D_c\le D .$$
--
--   The terms of $c$ are products $z_az_b$ of distinct pairs, hence orthonormal, and the shared bit lies in at most $D$ equations besides the central one.
--
--   **Formalization Note.** The sum $\sum_{a<b}d_{iab}d_{iab}$ is the number of terms of $c$, written as a count. Both conclusions, the identity and the bound, are stated.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 7, Section II, (31)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_31 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (i : Fin m) (r : Fin 3) :
    avgZ (fun x => cPoly tri rhs i r x ^ 2) = (termCount tri i r : ℝ) ∧
      termCount tri i r ≤ D := by sorry

end QAOAE3Lin2.General
