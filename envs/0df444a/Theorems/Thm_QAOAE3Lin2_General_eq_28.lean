-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_28
-- name    : QAOAE3Lin2.General.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:19.022528+00:00
-- url     : https://prove2.me/theorems/92b669ba-2483-43ad-aa98-cbfb360f3e96
-- title:
--   Section II, (26)–(28), p. 6 — Taylor remainder |R^k| ≤ ⅛(|γ|^{k+2}/(k+2)!)E_z[Σ|d ± c₁ ± c₂ ± c₃|^{k+2}] for odd k
-- statement:
--   Fix a Max E3LIN2 instance, an equation with sign $d$ and polynomials $c_1,c_2,c_3$, and an odd $k$. Expand (25) as
--   $$\tfrac12d^2\gamma+P^k(\gamma)+R^k(\gamma)$$
--   with $P^k$ as in (27). Then for every real $\gamma$ the remainder satisfies
--   $$|R^k(\gamma)|\le\frac18\,\frac{|\gamma|^{k+2}}{(k+2)!}\,E_z\big[|d+c_1+c_2+c_3|^{k+2}+|d+c_1-c_2-c_3|^{k+2}+|d-c_1+c_2-c_3|^{k+2}+|d-c_1-c_2+c_3|^{k+2}\big].$$
--
--   This isolates the linear term $\tfrac12\gamma$ of each clause and bounds what is left after the polynomial part.
--
--   **Formalization Note.** $R^k$ is defined by (26) as (25) minus $\tfrac12d^2\gamma$ minus $P^k(\gamma)$, so the statement is the remainder bound (28). $k$ is odd, as in (27)'s sum $j=3,5,\dots,k$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 6, Section II, (26)–(28)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_28 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (k : ℕ) (hk : Odd k) (γ : ℝ) :
    |Rk tri rhs i k γ| ≤ (1 / 8) * |γ| ^ (k + 2) / ((k + 2).factorial : ℝ) *
      avgZ (fun x =>
        let d := sgn rhs i
        let c₁ := cPoly tri rhs i 0 x
        let c₂ := cPoly tri rhs i 1 x
        let c₃ := cPoly tri rhs i 2 x
        |d + c₁ + c₂ + c₃| ^ (k + 2) + |d + c₁ - c₂ - c₃| ^ (k + 2) +
          |d - c₁ + c₂ - c₃| ^ (k + 2) + |d - c₁ - c₂ + c₃| ^ (k + 2)) := by sorry

end QAOAE3Lin2.General
