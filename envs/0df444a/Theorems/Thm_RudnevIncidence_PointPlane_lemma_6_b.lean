-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_lemma_6_b
-- name    : RudnevIncidence.PointPlane.lemma_6_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:47.812387+00:00
-- url     : https://prove2.me/theorems/1c8f447c-3084-481f-b779-630c97265fde
-- title:
--   Lemma 6 (second statement), p. 10 — over an algebraically closed field, K ∩ S₁ ∩ S₂ = K ∩ S₁ ∩ T_L K for some L ∈ K
-- statement:
--   Let $\mathbb F$ be algebraically closed. Let $S_1,S_2$ be two distinct hyperplanes of $\mathbb P^5$, given by linearly independent covectors $U_1,U_2\in\mathbb F^6$, and suppose $\mathcal K\cap S_1$ is the Klein image of a regular line complex, i.e. $S_1$ is not tangent to the Klein quadric. Then there is a line $l$ of $\mathbb P^3$, spanned by linearly independent $q,u$, with Plücker vector $L$, such that
--   $$\mathcal K\cap S_1\cap S_2=\mathcal K\cap S_1\cap T_L\mathcal K .$$
--   So $S_2$ may be replaced by the hyperplane $S_2'=T_L\mathcal K$ tangent to $\mathcal K$ at $L$, and $\mathcal K\cap S_2'$ is the Klein image of the singular line complex of lines meeting $l$.
--
--   This is the step that lets the proof read a section of $\mathcal G=\mathcal K\cap S_1$ by a three-dimensional subspace as the set of lines meeting a fixed line of $\mathbb P^3$.
--
--   **Formalization Note** The equality of the two point sets is stated pointwise for vectors $L'$ on the Klein quadric. The hypothesis $S_1\neq S_2$ (linear independence of $U_1,U_2$) is added: the page does not state it, but for $S_2=S_1$ the claim is false, since a regular line complex is not contained in a singular one. The tangent point $L$ is produced as the Plücker vector of an explicit line, so it lies on $\mathcal K$ and has a Klein pre-image.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, pp. 9–10, Lemma 6, second statement

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem lemma_6_b {F : Type*} [Field F] [IsAlgClosed F] (U₁ U₂ : Fin 6 → F)
    (h₁ : NonTangent U₁) (h₁₂ : LinearIndependent F ![U₁, U₂]) :
    ∃ q u : Fin 4 → F, LinearIndependent F ![q, u] ∧
      ∀ L' : Fin 6 → F, klein L' = 0 →
        (L' ∈ hyperplane U₁ ⊓ hyperplane U₂ ↔
          L' ∈ hyperplane U₁ ⊓ tangentHyperplane (plucker q u)) := by sorry
end RudnevIncidence.PointPlane
