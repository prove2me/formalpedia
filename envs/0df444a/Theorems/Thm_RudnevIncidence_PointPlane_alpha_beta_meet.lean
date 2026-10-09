-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_alpha_beta_meet
-- name    : RudnevIncidence.PointPlane.alpha_beta_meet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:39.4299+00:00
-- url     : https://prove2.me/theorems/b6ab52d2-9823-4cca-9aca-1fbd71a98260
-- title:
--   §4.1.1, p. 9 — two α-planes or two β-planes meet at a point; an α- and a β-plane meet along a line iff q ∈ π, else not at all
-- statement:
--   For a point $q$ of $\mathbb P^3$ let $\alpha(q)\subseteq\mathbb F^6$ be its α-plane (the span of the Plücker vectors of the lines through $q$), and for a plane $\pi$ let $\beta(\pi)$ be its β-plane (the span of the Plücker vectors of the lines in $\pi$). Then:
--
--   1. for distinct points $q\neq q'$, $\alpha(q)\cap\alpha(q')$ is the 1-dimensional span of the Plücker vector of the line $qq'$, i.e. the two α-planes meet at the point of $\mathbb P^5$ representing the line through the two concurrency points;
--   2. for distinct planes $\pi\neq\pi'$, $\beta(\pi)\cap\beta(\pi')$ is 1-dimensional, i.e. the two β-planes meet at a point;
--   3. for a point $q$ and a plane $\pi$,
--   $$\dim\big(\alpha(q)\cap\beta(\pi)\big)=\begin{cases}2,& q\in\pi,\\ 0,& q\notin\pi,\end{cases}$$
--   i.e. an α- and a β-plane meet along a line of $\mathbb P^5$ exactly when $q\in\pi$, and do not meet otherwise.
--
--   This dictionary converts point–plane incidences in $\mathbb P^3$ into incidences between planes of the two rulings of the Klein quadric, the first step towards Lemma 9.
--
--   **Formalization Note** Dimensions are vector-space dimensions of subspaces of $\mathbb F^6$: a projective point is dimension 1, a projective line dimension 2, and "do not meet" is dimension 0. The representative of a projective point or plane is Mathlib's `Projectivization.rep`. The statement holds over every field.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 9, §4.1.1, paragraph "Two planes of the same ruling of K always meet at a point …"

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem alpha_beta_meet {F : Type*} [Field F] :
    (∀ q q' : ℙ F (Fin 4 → F), q ≠ q' →
      alphaPlane q ⊓ alphaPlane q' = Submodule.span F {plucker q.rep q'.rep} ∧
        Module.finrank F ↥(alphaPlane q ⊓ alphaPlane q') = 1) ∧
    (∀ π π' : ℙ F (Fin 4 → F), π ≠ π' →
      Module.finrank F ↥(betaPlane π ⊓ betaPlane π') = 1) ∧
    (∀ q π : ℙ F (Fin 4 → F),
      Module.finrank F ↥(alphaPlane q ⊓ betaPlane π) = if q.orthogonal π then 2 else 0) := by sorry
end RudnevIncidence.PointPlane
