-- Prove2me | Theorems.Thm_RunIntersect_Facet_mp_full_dimensional
-- name    : RunIntersect.Facet.mp_full_dimensional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:16.647195+00:00
-- url     : https://prove2.me/theorems/b4f715ce-fd46-42a1-b400-78b875d4beb9
-- title:
--   p. 1016, proof of Proposition 4 (citing [12]) — MP_G is full dimensional
-- statement:
--   Let $G=(V,E)$ be a hypergraph without loops or parallel edges. Then the multilinear polytope $\mathrm{MP}_G\subseteq\mathbb R^{V+E}$ is full dimensional:
--   $$\dim \mathrm{MP}_G=|V|+|E|.$$
--
--   The paper cites this fact from Del Pia and Khajavirad, *A polyhedral study of binary polynomial programs* (Math. Oper. Res. 2017); it reduces "defines a facet" to "every valid inequality tight on the same points is a positive multiple".
--
--   **Formalization Note** The dimension is the rank of the vector span of $\mathrm{MP}_G$ inside `α ⊕ Finset α → ℝ`, in which the coordinates outside $V+E$ are pinned to zero.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1016, proof of Proposition 4 (citing Del Pia and Khajavirad [12])

import Mathlib
import Definitions.Def_RunIntersect_Facet_Setting

namespace RunIntersect.Facet

/-- p. 1016 (cited from Del Pia and Khajavirad [12]): the multilinear polytope is full
dimensional in `ℝ^{V+E}`. -/
theorem mp_full_dimensional {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) :
    Module.finrank ℝ (vectorSpan ℝ (MP G)) = G.V.card + G.E.card := by sorry

end RunIntersect.Facet
