-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_projection_argument
-- name    : RudnevIncidence.PointPlane.projection_argument
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:39.74302+00:00
-- url     : https://prove2.me/theorems/e70095af-9df7-4240-be9e-8b712ea0af53
-- title:
--   §5, p. 14 — over an infinite field a finite line arrangement in P⁴ projects to P³ one-to-one, preserving incidences and skewness
-- statement:
--   Let $\mathbb F$ be an infinite field and $\mathcal L$ a finite set of lines of $\mathbb P^4$, i.e. 2-dimensional subspaces of $\mathbb F^5$. Then there is a surjective linear map $f:\mathbb F^5\to\mathbb F^4$ (a projection of $\mathbb P^4$ from a point onto a three-hyperplane) such that
--
--   1. every line of $\mathcal L$ is mapped onto a line of $\mathbb P^3$;
--   2. distinct lines of $\mathcal L$ have distinct images;
--   3. two lines of $\mathcal L$ meet if and only if their images meet; in particular skew lines remain skew.
--
--   So the projected arrangement has the same number of lines and the same number of incidences. The proof of Theorem 12 uses this to move the lines of $\mathcal G\subset\mathbb P^4$ into $\mathbb P^3$, where polynomial methods apply.
--
--   **Formalization Note** $\mathbb P^4$ is modelled on $\mathbb F^5$ (in the application it is the hyperplane $S\subset\mathbb P^5$ after a choice of coordinates). The page also says that the set of good projection centres is Zariski open; only its non-emptiness, which is what the proof uses, is stated.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 14, §5, paragraph "The key issue is that any finite line arrangement …"; used on p. 15

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem projection_argument {F : Type*} [Field F] [Infinite F]
    (𝓛 : Finset (Submodule F (Fin 5 → F))) (h𝓛 : ∀ W ∈ 𝓛, Module.finrank F W = 2) :
    ∃ f : (Fin 5 → F) →ₗ[F] (Fin 4 → F), Function.Surjective f ∧
      (∀ W ∈ 𝓛, Module.finrank F ↥(W.map f) = 2) ∧
      Set.InjOn (Submodule.map f) (𝓛 : Set (Submodule F (Fin 5 → F))) ∧
      ∀ W ∈ 𝓛, ∀ W' ∈ 𝓛, (W.map f ⊓ W'.map f = ⊥ ↔ W ⊓ W' = ⊥) := by sorry
end RudnevIncidence.PointPlane
