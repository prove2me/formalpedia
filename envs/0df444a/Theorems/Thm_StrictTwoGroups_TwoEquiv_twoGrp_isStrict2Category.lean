-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_twoGrp_isStrict2Category
-- name    : StrictTwoGroups.TwoEquiv.twoGrp_isStrict2Category
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:34.400999+00:00
-- url     : https://prove2.me/theorems/2d935f08-b54f-45e9-b4a1-450808f51a1e
-- title:
--   §2, p. 7, Definition — strict 2-groups, internal functors and internal natural transformations form the 2-category 2-Grp
-- statement:
--   Strict 2-groups, their morphisms (functors in the category of groups) and their 2-morphisms (natural transformations in the category of groups), with componentwise composition of morphisms, vertical composition $(\bar\vartheta\bullet\vartheta)(g)=\bar\vartheta g\circ'\vartheta g$, horizontal composition
--   $$(\vartheta'\circ\vartheta)(g)=\vartheta'(E_0g)\circ''F'_1(\vartheta g)$$
--   and identity 2-cells $g\mapsto i'(F_0g)$, form a 2-category $2\text{-}\mathit{Grp}$: lawful cells are closed under all compositions and identities, every hom $2\text{-}\mathit{Grp}(\mathcal G,\mathcal G')$ is a category, horizontal composition is a functor (identities and interchange law), it is associative, and identities are units.
--
--   This is the source 2-category of the 2-equivalence of §6.
--
--   **Formalization Note** `IsStrict2Category twoGrp` quantifies over lawful objects, 1-cells and 2-cells only. Compositions are written diagrammatically.
--
--   Differences from the source:
--   - encoding: 2-categories given by their cells, compositions and identities; morphisms and 2-morphisms are group morphisms / maps with their source and target → raw data (Raw2Cat) with lawfulness predicates IsOb, Is1, Is2, every law quantified over lawful cells only; 2-cells typed by their objects with the boundary 1-cells as explicit arguments; cells are plain functions and "is a group morphism" is a clause of Is1 / Is2; reason: changes no instance: the lawful objects, 1-cells and 2-cells are exactly the paper's, and nothing is asserted about the others.
--   - encoding: applicative composition (γ′ ∘ γ, η′ ∘ η, E ∘ F) → diagrammatic comp1 f g, vcomp, hcomp and Raw2Functor.comp ("first, then second"); reason: notation only; every composite is the same map as on the page.
--   - encoding: composition ∘ : G1 s×t G1 → G1 of a strict 2-group → total function comp : G1 → G1 → G1 with every axiom stated on composable pairs; reason: values off the pullback are never constrained or used.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 7, §2 Definition (2-Grp); p. 5, §1 Example (internal categories form a 2-category)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_TwoGrp

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §2, p. 7, Definition (with §1, p. 5, Example): strict 2-groups, their morphisms and their
2-morphisms form a 2-category `2-Grp`. -/
theorem twoGrp_isStrict2Category : Raw2Cat.IsStrict2Category twoGrp.{u} := by sorry

end StrictTwoGroups.TwoEquiv
