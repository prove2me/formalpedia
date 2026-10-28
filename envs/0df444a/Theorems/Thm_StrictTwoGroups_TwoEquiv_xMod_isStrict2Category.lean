-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_xMod_isStrict2Category
-- name    : StrictTwoGroups.TwoEquiv.xMod_isStrict2Category
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:39.45446+00:00
-- url     : https://prove2.me/theorems/43d336a8-627e-4b32-a955-e1c2fa1a0097
-- title:
--   §3, p. 10, Proposition and Definition — crossed modules form the 2-category X-Mod
-- statement:
--   Crossed modules, crossed module morphisms and crossed module 2-morphisms, with componentwise composition of morphisms, the constant identity 2-cells $g\mapsto e$, vertical composition $(\bar\eta\bullet\eta)(g)=\bar\eta g\,\eta g$ and horizontal composition
--   $$(\eta'\circ\eta)(g)=\Delta'(\eta g)\cdot\eta'(\gamma g),$$
--   form a 2-category $X\text{-}\mathit{Mod}$: lawful cells are closed under all compositions and identities, every hom $X\text{-}\mathit{Mod}(\chi,\chi')$ is a category, horizontal composition is a functor (identities and interchange law), it is associative, and identities are units.
--
--   This is the target 2-category of the 2-equivalence of §6.
--
--   **Formalization Note** `IsStrict2Category xMod` quantifies over lawful objects, 1-cells and 2-cells only; compositions are diagrammatic. The interchange law is part of "composition functor" in the paper's definition of a 2-category (p. 4), so it is included although p. 10 does not display its verification.
--
--   Differences from the source:
--   - encoding: 2-categories given by their cells, compositions and identities; morphisms and 2-morphisms are group morphisms / maps with their source and target → raw data (Raw2Cat) with lawfulness predicates IsOb, Is1, Is2, every law quantified over lawful cells only; 2-cells typed by their objects with the boundary 1-cells as explicit arguments; cells are plain functions and "is a group morphism" is a clause of Is1 / Is2; reason: changes no instance: the lawful objects, 1-cells and 2-cells are exactly the paper's, and nothing is asserted about the others.
--   - encoding: applicative composition (γ′ ∘ γ, η′ ∘ η, E ∘ F) → diagrammatic comp1 f g, vcomp, hcomp and Raw2Functor.comp ("first, then second"); reason: notation only; every composite is the same map as on the page.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 10, §3 Proposition and Definition

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_XMod

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §3, p. 10, Proposition and Definition: crossed modules, crossed module morphisms and crossed
module 2-morphisms form a 2-category `X-Mod`. -/
theorem xMod_isStrict2Category : Raw2Cat.IsStrict2Category xMod.{u} := by sorry

end StrictTwoGroups.TwoEquiv
