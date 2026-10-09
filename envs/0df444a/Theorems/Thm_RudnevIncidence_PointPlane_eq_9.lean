-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_eq_9
-- name    : RudnevIncidence.PointPlane.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:54.983153+00:00
-- url     : https://prove2.me/theorems/30715a89-ee26-4ab8-a26c-d76a21c8e4df
-- title:
--   (9), §4.1, p. 8 — two lines of P³ meet iff the reciprocal product of their Plücker vectors vanishes
-- statement:
--   Let $l$ be the line of $\mathbb P^3$ through two linearly independent vectors $q,u\in\mathbb F^4$, and $l'$ the line through linearly independent $q',u'$. Let $L$ and $L'$ be their Plücker vectors. Then $l$ and $l'$ meet if and only if
--   $$P_{01}P'_{23}+P_{02}P'_{31}+P_{03}P'_{12}+P'_{01}P_{23}+P'_{02}P_{31}+P'_{03}P_{12}=0.$$
--
--   This incidence criterion is what turns incidence questions about lines of $\mathbb P^3$ into linear algebra on the Klein quadric $\mathcal K\subset\mathbb P^5$: two lines meet exactly when each Plücker vector lies in the tangent hyperplane of the other.
--
--   **Formalization Note** The lines are the spans of $\{q,u\}$ and $\{q',u'\}$ in $\mathbb F^4$; "meet" means that the two spans have a nonzero common vector. The statement holds over every field.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 8, §4.1, (9)

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem eq_9 {F : Type*} [Field F] (q u q' u' : Fin 4 → F)
    (h : LinearIndependent F ![q, u]) (h' : LinearIndependent F ![q', u']) :
    Submodule.span F {q, u} ⊓ Submodule.span F {q', u'} ≠ ⊥ ↔
      recip (plucker q u) (plucker q' u') = 0 := by sorry
end RudnevIncidence.PointPlane
