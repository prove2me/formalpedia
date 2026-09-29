-- Prove2me | Theorems.Thm_RovelliLQG_minkowski_spin_geometry
-- name    : RovelliLQG.minkowski_spin_geometry
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T19:31:54.222121+00:00
-- url     : https://prove2.me/theorems/ffbed532-0b7a-448f-869e-11970bbb4974
-- title:
--   Spin–geometry theorem (Minkowski 1897): closed normals determine a unique polyhedron
-- statement:
--   Let $n_1,\dots,n_v\in\mathbb R^3$ be nonzero vectors such that
--
--   1. their directions $\hat n_l=n_l/\|n_l\|$ are pairwise distinct,
--   2. they span $\mathbb R^3$,
--   3. they satisfy the closure relation $\displaystyle\sum_{l=1}^v n_l=0$.
--
--   Then there are support numbers $h_1,\dots,h_v$ such that the polyhedron $P=\{x:\langle\hat n_l,x\rangle\le h_l\ \forall l\}$ is bounded, has nonempty interior, and its $l$-th face $F_l=P\cap\{\langle\hat n_l,x\rangle=h_l\}$ has area
--   $$\operatorname{area}(F_l)=\|n_l\|\qquad(l=1,\dots,v).$$
--   Moreover, any two families of support numbers with this property give polyhedra that are translates of one another.
--
--   This is the extended Penrose spin–geometry theorem of §2.1: vectors satisfying the closure relation (6) are the area vectors of a flat polyhedron with $v$ faces, unique up to translation, so each node of a spin network carries a geometry.
--
--   **Formalization Note** The spanning and distinct-direction hypotheses are the standard non-degeneracy conditions of Minkowski's theorem, left implicit in the review. Areas are compared in $[0,\infty]$.
-- source:
--   C. Rovelli, Loop quantum gravity: the first 25 years, Class. Quantum Grav. 28 (2011) 153002, doi:10.1088/0264-9381/28/15/153002, arXiv:1012.4707, §2.1, pp. 4-5, text following eqs. (6)-(9) (extended spin-geometry theorem, citing Minkowski 1897 [24])

import Mathlib
import Definitions.Def_RovelliLQG_Defs

open scoped InnerProductSpace

namespace RovelliLQG

theorem minkowski_spin_geometry {v : ℕ} (n : Fin v → E3)
    (hne : ∀ l, n l ≠ 0)
    (hdir : ∀ l l', l ≠ l' → unitDir (n l) ≠ unitDir (n l'))
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (hclosure : ∑ l, n l = 0) :
    (∃ h : Fin v → ℝ,
      Bornology.IsBounded (halfspacePolyhedron (fun l => unitDir (n l)) h) ∧
      (interior (halfspacePolyhedron (fun l => unitDir (n l)) h)).Nonempty ∧
      ∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h l) =
        ENNReal.ofReal ‖n l‖) ∧
    (∀ h h' : Fin v → ℝ,
      (∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h l) =
        ENNReal.ofReal ‖n l‖) →
      (∀ l, planarArea (n l) (polyhedronFace (fun l => unitDir (n l)) h' l) =
        ENNReal.ofReal ‖n l‖) →
      ∃ t : E3, halfspacePolyhedron (fun l => unitDir (n l)) h' =
        (fun x => x + t) '' halfspacePolyhedron (fun l => unitDir (n l)) h) := by
  sorry

end RovelliLQG
