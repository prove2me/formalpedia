-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_lemma_6_a
-- name    : RudnevIncidence.PointPlane.lemma_6_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:48.412351+00:00
-- url     : https://prove2.me/theorems/4acff305-6258-4f86-92b2-cde7fa3d827c
-- title:
--   Lemma 6 (first statement), p. 9 — K ∩ T_L K contains the α-planes of points on l and the β-planes of planes containing l
-- statement:
--   Let $l$ be the line of $\mathbb P^3$ spanned by linearly independent $q,u\in\mathbb F^4$, with Plücker vector $L$, and let $T_L\mathcal K=\{L':\langle L,L'\rangle=0\}$ be the tangent hyperplane to the Klein quadric $\mathcal K$ at $L$. Then $\mathcal K\cap T_L\mathcal K$ contains
--
--   1. the α-plane of every point $x$ on $l$, and
--   2. the β-plane of every plane $\pi$ containing $l$.
--
--   That is, each such α- or β-plane lies both in $T_L\mathcal K$ and in $\mathcal K$. Together with the second statement of Lemma 6 this identifies a three-dimensional section of $\mathcal G$ with the lines meeting a fixed line, which is how the collinearity parameter $k$ enters the proof of Theorem 3.
--
--   **Formalization Note** "Contains" is read as stated: each listed α- or β-plane is a subspace of $T_L\mathcal K$ on which the Klein form vanishes; the converse (that these are the only α- and β-planes in $T_L\mathcal K$) is not claimed. Holds over every field.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, pp. 9–10, Lemma 6, first statement

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem lemma_6_a {F : Type*} [Field F] (q u : Fin 4 → F)
    (hqu : LinearIndependent F ![q, u]) :
    (∀ x : ℙ F (Fin 4 → F), x.rep ∈ Submodule.span F {q, u} →
      alphaPlane x ≤ tangentHyperplane (plucker q u) ∧ ∀ L ∈ alphaPlane x, klein L = 0) ∧
    (∀ π : ℙ F (Fin 4 → F), (∀ w ∈ Submodule.span F {q, u}, w ⬝ᵥ π.rep = 0) →
      betaPlane π ≤ tangentHyperplane (plucker q u) ∧ ∀ L ∈ betaPlane π, klein L = 0) := by sorry
end RudnevIncidence.PointPlane
