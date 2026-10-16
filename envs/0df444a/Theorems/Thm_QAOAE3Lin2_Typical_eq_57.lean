-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_57
-- name    : QAOAE3Lin2.Typical.eq_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:07.811903+00:00
-- url     : https://prove2.me/theorems/3d9f8691-68d7-4d8e-a24b-0f45e8c82192
-- title:
--   Section III, (57), p. 11 — clause terms whose (25) expressions share no d are uncorrelated over the d's
-- statement:
--   Let the triples form an E3LIN2 family and let $\gamma\in\mathbb R$. For an equation $abc$, call its **dependency set** the equation itself together with all equations sharing exactly one bit with it: these are the $d$'s that appear in (25) for $abc$. If the dependency sets of two equations $abc$ and $a'b'c'$ are disjoint, then, averaging over uniformly random right-hand sides,
--   $$\mathbb E_d\Big[T_{abc}\,T_{a'b'c'}\Big]=\mathbb E_d\big[T_{abc}\big]\cdot\mathbb E_d\big[T_{a'b'c'}\big],\qquad T_{abc}=\tfrac12 d_{abc}\langle-\gamma,\pi/4|Z_aZ_bZ_c|-\gamma,\pi/4\rangle .$$
--
--   Only pairs of linked equations therefore contribute to the variance of (55).
--
--   **Formalization Note** The paper's (57) is written for $d_{abc}\langle\cdots\rangle$ without the factor $\tfrac12$ of (55); both sides of the identity scale by $\tfrac14$, so the statement is the same. The dependency set contains the equation itself, so two terms sharing their own $d$ are never declared unlinked.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 11, Section III, (56)–(57)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- (57), p. 11: if no sign `d` appearing in (25) for equation `i` appears in (25) for equation
`i'`, the two clause terms are uncorrelated over the instances. -/
theorem eq_57 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i i' : Fin m) (hdis : Disjoint (deps tri i) (deps tri i')) (γ : ℝ) :
    avgD (fun rhs => clauseTerm tri rhs i γ * clauseTerm tri rhs i' γ) =
      avgD (fun rhs => clauseTerm tri rhs i γ) *
        avgD (fun rhs => clauseTerm tri rhs i' γ) := by sorry

end QAOAE3Lin2.Typical
