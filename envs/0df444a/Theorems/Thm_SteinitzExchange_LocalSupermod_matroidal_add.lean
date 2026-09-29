-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_matroidal_add
-- name    : SteinitzExchange.LocalSupermod.matroidal_add
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:50:10.11555+00:00
-- url     : https://prove2.me/theorems/ea300d8c-b33a-4f85-bd59-fe3be9e9b3a2
-- title:
--   Lemma 5.2 — the sum of two "matroidal" functions is "matroidal"
-- statement:
--   Let $h_1,h_2:\mathbb R^V\to\mathbb R$ be positively homogeneous functions. If $h_1$ and $h_2$ are "matroidal" (satisfy (C1) and (C2)), then
--
--   $$h_1+h_2\ \text{is "matroidal"}.$$
--
--   In the language of base polytopes this is the statement that the Minkowski sum of two integral base polytopes has a "matroidal" support function; the paper uses it for the duality results of Section 6.
--
--   **Formalization Note.** Positive homogeneity of $h_1,h_2$ is listed as on the page, although it is already part of "matroidal" in the formal definition.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 291, Lemma 5.2

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 291, Lemma 5.2. If positively homogeneous `h₁, h₂ : ℝ^V → ℝ` are
"matroidal", then `h₁ + h₂` is "matroidal". -/
theorem matroidal_add {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (h₁ h₂ : (V → ℝ) → ℝ) (hh₁ : IsPosHomogeneous h₁) (hh₂ : IsPosHomogeneous h₂)
    (hm₁ : IsMatroidal h₁) (hm₂ : IsMatroidal h₂) :
    IsMatroidal (h₁ + h₂) := by sorry

end SteinitzExchange.LocalSupermod
