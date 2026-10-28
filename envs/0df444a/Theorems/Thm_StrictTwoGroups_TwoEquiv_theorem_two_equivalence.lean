-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_theorem_two_equivalence
-- name    : StrictTwoGroups.TwoEquiv.theorem_two_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:42.940153+00:00
-- url     : https://prove2.me/theorems/9fb0bf80-b849-4b2b-83d6-2808dd37122f
-- title:
--   Theorem, §6, p. 16 — the 2-categories 2-Grp and X-Mod are 2-equivalent
-- statement:
--   The 2-category $2\text{-}\mathit{Grp}$ of strict 2-groups (internal categories in the category of groups, with internal functors and internal natural transformations) and the 2-category $X\text{-}\mathit{Mod}$ of crossed modules (with crossed module morphisms and 2-morphisms) are 2-equivalent:
--   $$2\text{-}\mathit{Grp}\ \simeq\ X\text{-}\mathit{Mod}.$$
--   That is, both are 2-categories, and there are 2-functors $F:2\text{-}\mathit{Grp}\to X\text{-}\mathit{Mod}$ and $E:X\text{-}\mathit{Mod}\to2\text{-}\mathit{Grp}$ together with 2-natural isomorphisms $E\circ F\cong\mathrm{id}_{2\text{-}\mathit{Grp}}$ and $F\circ E\cong\mathrm{id}_{X\text{-}\mathit{Mod}}$.
--
--   The theorem lets one pass freely between strict 2-groups, suited to categorical reasoning, and crossed modules, suited to computation. The paper's witnesses are $F=T$, $E=S$ and the round-trip isomorphisms $\xi$, $\zeta$, which are the milestones.
--
--   **Formalization Note** The 2-categories are the concrete `twoGrp` and `xMod`. `TwoEquivalent` includes that both satisfy all 2-category axioms, that both 2-functors preserve vertical and horizontal composition and identities on 2-cells as well as 1-cells, and that the 2-natural isomorphisms satisfy the 2-cell part of diagram (7). All groups live in one universe.
--
--   Differences from the source:
--   - encoding: groups of arbitrary size → all groups in one universe `u`, the statement holding for every `u`; reason: Lean's universe stratification; every set-sized group lives in some universe.
--   - encoding: 2-categories given by their cells, compositions and identities; morphisms and 2-morphisms are group morphisms / maps with their source and target → raw data (Raw2Cat) with lawfulness predicates IsOb, Is1, Is2, every law quantified over lawful cells only; 2-cells typed by their objects with the boundary 1-cells as explicit arguments; cells are plain functions and "is a group morphism" is a clause of Is1 / Is2; reason: changes no instance: the lawful objects, 1-cells and 2-cells are exactly the paper's, and nothing is asserted about the others.
--   - encoding: applicative composition (γ′ ∘ γ, η′ ∘ η, E ∘ F) → diagrammatic comp1 f g, vcomp, hcomp and Raw2Functor.comp ("first, then second"); reason: notation only; every composite is the same map as on the page.
--   - encoding: composition ∘ : G1 s×t G1 → G1 of a strict 2-group → total function comp : G1 → G1 → G1 with every axiom stated on composable pairs; reason: values off the pullback are never constrained or used.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 16, §6 Theorem

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §6, p. 16, Theorem: the 2-categories `2-Grp` and `X-Mod` are 2-equivalent. -/
theorem theorem_two_equivalence : TwoEquivalent twoGrp.{u} xMod.{u} := by sorry

end StrictTwoGroups.TwoEquiv
