-- Prove2me | Theorems.Thm_VanderbeiLP_StrictComp_separation_polyhedra
-- name    : VanderbeiLP.StrictComp.separation_polyhedra
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T17:50:10.079113+00:00
-- url     : https://prove2.me/theorems/58230981-1380-4452-bd28-60f85366e690
-- title:
--   Theorem 10.4 — Separation Theorem for polyhedra
-- statement:
--   Let $P$ and $\tilde P$ be two polyhedra in $\mathbb{R}^n$, i.e. sets of the form $\{x : Ax \le b\}$ and $\{x : \tilde A x \le \tilde b\}$. If $P$ and $\tilde P$ are both nonempty and disjoint, then there exist halfspaces $H$ and $\tilde H$ with
--
--   $$P \subseteq H, \qquad \tilde P \subseteq \tilde H, \qquad H \cap \tilde H = \emptyset.$$
--
--   Here a halfspace is a set $\{x : a^T x \le \beta\}$ with $a \ne 0$, so the two separating sets are genuine halfspaces with nonzero (and necessarily opposite-pointing) normals, not all of $\mathbb{R}^n$ or the empty set.
--
--   The theorem is the polyhedral case of the separating hyperplane theorem, obtained without any topology.
--
--   **Formalization Note** The book's "$P \subset H$" is inclusion (not necessarily proper). Both nonemptiness hypotheses are kept: they are what forces the normals to be nonzero.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 145, Theorem 10.4 (PDF p. 158); halfspace Eq. (10.3), p. 144

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_Polyhedron

namespace VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 10.4 (p. 145), Separation Theorem for polyhedra.** Two disjoint
nonempty polyhedra `P`, `P̃` of `ℝⁿ` lie in disjoint halfspaces `H ⊇ P`, `H̃ ⊇ P̃`
(halfspaces in the sense of (10.3): nonzero normal). -/
theorem separation_polyhedra {n : ℕ} (P Ptil : Set (Fin n → ℝ))
    (hP : IsPolyhedron P) (hPtil : IsPolyhedron Ptil)
    (hPne : P.Nonempty) (hPtilne : Ptil.Nonempty) (hdisj : Disjoint P Ptil) :
    ∃ H Htil : Set (Fin n → ℝ), IsHalfspace H ∧ IsHalfspace Htil ∧ Disjoint H Htil ∧
      P ⊆ H ∧ Ptil ⊆ Htil := by sorry

end VanderbeiLP.StrictComp
