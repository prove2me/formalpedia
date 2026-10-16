-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_47
-- name    : QAOAE3Lin2.Typical.eq_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:56.650637+00:00
-- url     : https://prove2.me/theorems/fd894edc-5e35-4740-88c1-90f484e1605b
-- title:
--   Section III, (47), p. 9 — averaging over d₁₂₃ alone, the clause term becomes ½(sin γ)E_z[cos(γc₁)cos(γc₂)cos(γc₃)]
-- statement:
--   Let the triples form an E3LIN2 family, fix right-hand sides for all equations, an equation $i$ (with bits $1,2,3$) and $\gamma\in\mathbb R$. Average the clause term $\tfrac12 d_{123}\langle-\gamma,\pi/4|Z_1Z_2Z_3|-\gamma,\pi/4\rangle$ over the two choices of the right-hand side of equation $i$ alone, keeping all other right-hand sides fixed. The result is
--   $$\tfrac12(\sin\gamma)\,\mathbb E_z\big[\cos(\gamma c_1)\cos(\gamma c_2)\cos(\gamma c_3)\big],$$
--   where $c_1,c_2,c_3$ are the polynomials (21) of equation $i$, which do not involve $d_{123}$.
--
--   In the paper's terms, the average of (24) over $d_{123}$ vanishes and (23) becomes (47). This is the first step of the average-case computation.
--
--   **Formalization Note** The average over $d_{123}$ is written as the mean of the clause term at the instance with right-hand side $0$ and at the instance with right-hand side $1$ for equation $i$. The polynomials $c_\rho$ on the right are evaluated at the given right-hand sides; they do not depend on the right-hand side of equation $i$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 9, Section III, (47)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- (47), p. 9: averaging the clause term of equation `i` over its own sign `d₁₂₃` alone gives
`½ (sin γ) E_z[cos(γc₁) cos(γc₂) cos(γc₃)]` (the `c`'s do not involve `d₁₂₃`). -/
theorem eq_47 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) :
    (clauseTerm tri (Function.update rhs i false) i γ +
        clauseTerm tri (Function.update rhs i true) i γ) / 2 =
      (1 / 2) * Real.sin γ * QAOAE3Lin2.General.avgZ (fun x => Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i 0 x) *
        Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i 1 x) * Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i 2 x)) := by sorry

end QAOAE3Lin2.Typical
