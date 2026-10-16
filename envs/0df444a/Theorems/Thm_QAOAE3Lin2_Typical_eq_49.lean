-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_49
-- name    : QAOAE3Lin2.Typical.eq_49
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:08.81965+00:00
-- url     : https://prove2.me/theorems/1bbafe22-d9fa-49f8-979a-d67f74ff0a5d
-- title:
--   Section III, (49), p. 10 — E_d of the clause term is ½(sin γ)(cos γ)^{D₁+D₂+D₃}, with D₁ + D₂ + D₃ ⩽ 3D
-- statement:
--   Let the triples form an E3LIN2 family in which every bit lies in at most $D+1$ equations. Fix an equation $i$ and $\gamma\in\mathbb R$, and let $D_1,D_2,D_3$ be the numbers of terms of its polynomials $c_1,c_2,c_3$ (21). Averaging over the $2^m$ right-hand-side vectors,
--   $$\mathbb E_d\Big[\tfrac12 d_{123}\langle-\gamma,\pi/4|Z_1Z_2Z_3|-\gamma,\pi/4\rangle\Big]=\tfrac12(\sin\gamma)(\cos\gamma)^{D_1+D_2+D_3},$$
--   and
--   $$0\le D_1+D_2+D_3\le 3D .$$
--
--   Summed over the $m$ equations this gives the mean bound (50).
--
--   **Formalization Note** $D_\rho$ counts the equations $j\neq i$ that share exactly the role-$\rho$ bit with equation $i$. The bound $0\le D_1+D_2+D_3$ is automatic for natural numbers and is not restated.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 10, Section III, (49)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- (49), p. 10: the average over the instances of the clause term of equation `i` is
`½ (sin γ)(cos γ)^{D₁+D₂+D₃}`, and `D₁ + D₂ + D₃ ≤ 3D`. -/
theorem eq_49 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (i : Fin m) (γ : ℝ) :
    avgD (fun rhs => clauseTerm tri rhs i γ) =
        (1 / 2) * Real.sin γ *
          Real.cos γ ^ (QAOAE3Lin2.General.termCount tri i 0 + QAOAE3Lin2.General.termCount tri i 1 + QAOAE3Lin2.General.termCount tri i 2) ∧
      QAOAE3Lin2.General.termCount tri i 0 + QAOAE3Lin2.General.termCount tri i 1 + QAOAE3Lin2.General.termCount tri i 2 ≤ 3 * D := by sorry

end QAOAE3Lin2.Typical
