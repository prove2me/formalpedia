-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_32
-- name    : QAOAE3Lin2.General.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:35.446787+00:00
-- url     : https://prove2.me/theorems/9c71b161-f245-4118-8a37-c8467595ac9b
-- title:
--   Section II, (30)–(32), p. 7 — E_z[(d ± c₁ ± c₂ ± c₃)²] ≤ 1 + 9D
-- statement:
--   Under the hypotheses of (31), fix an equation with sign $d$ and polynomials $c_1,c_2,c_3$. For every choice of signs $\varepsilon_1,\varepsilon_2,\varepsilon_3\in\{\pm1\}$,
--   $$E_z\big[(d+\varepsilon_1c_1+\varepsilon_2c_2+\varepsilon_3c_3)^2\big]\le1+9D .$$
--
--   Together with hypercontractivity (29) this bounds every moment of the four clause arguments of (25).
--
--   **Formalization Note.** The paper's $\pm$ are independent, and all eight sign choices are covered. Lean's roles $0,1,2$ are the paper's $1,2,3$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 7, Section II, (30)–(32)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_32 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (i : Fin m)
    (ε : Fin 3 → ℝ) (hε : ∀ r, ε r = 1 ∨ ε r = -1) :
    avgZ (fun x => (sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x) ^ 2) ≤ 1 + 9 * (D : ℝ) := by sorry

end QAOAE3Lin2.General
