-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_S_isTwoFunctor
-- name    : StrictTwoGroups.TwoEquiv.S_isTwoFunctor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:42.627985+00:00
-- url     : https://prove2.me/theorems/1b694b45-4a14-49da-9e97-244ff52d0b22
-- title:
--   §5, p. 15 — S = (S₀, S₁, S₂) : X-Mod → 2-Grp is a 2-functor
-- statement:
--   The assignment
--   $$S_0(\chi)=(G,H\rtimes G,s,t,i),\qquad S_1(\gamma,\delta)=(\gamma,(\delta,\gamma)),\qquad S_2\eta=\bigl(g\mapsto(\eta g,\gamma g)\bigr)\ \text{ for }\eta:(\gamma,\delta)\Rightarrow(\Gamma,\Delta)$$
--   is a 2-functor $S:X\text{-}\mathit{Mod}\to2\text{-}\mathit{Grp}$: it sends crossed modules to strict 2-groups, morphisms to morphisms and 2-morphisms to 2-morphisms, each $S_{\chi,\chi'}$ is a functor, and $S$ preserves horizontal composition and identities of 1-cells and 2-cells.
--
--   **Formalization Note** `IsTwoFunctor S` has the same clauses as for $T$. $S_1(\gamma,\delta)$ acts on $H\rtimes G$ by $(h,g)\mapsto(\delta h,\gamma g)$. The paper's p. 14 writes "$S_1 i(G,H,\tau,\alpha)=T_1(\mathrm{id}_G,\mathrm{id}_H)$", where $S_1$ is meant, and expands the horizontal composite as $\eta'\gamma\cdot\delta'\eta$ where p. 9 has $\Delta'\eta\cdot\eta'\gamma=\eta'\Gamma\cdot\delta'\eta$; the definitions of p. 9 are used. Neither affects the statement.
--
--   Differences from the source:
--   - encoding: 2-categories given by their cells, compositions and identities; morphisms and 2-morphisms are group morphisms / maps with their source and target → raw data (Raw2Cat) with lawfulness predicates IsOb, Is1, Is2, every law quantified over lawful cells only; 2-cells typed by their objects with the boundary 1-cells as explicit arguments; cells are plain functions and "is a group morphism" is a clause of Is1 / Is2; reason: changes no instance: the lawful objects, 1-cells and 2-cells are exactly the paper's, and nothing is asserted about the others.
--   - encoding: applicative composition (γ′ ∘ γ, η′ ∘ η, E ∘ F) → diagrammatic comp1 f g, vcomp, hcomp and Raw2Functor.comp ("first, then second"); reason: notation only; every composite is the same map as on the page.
--   - encoding: composition ∘ : G1 s×t G1 → G1 of a strict 2-group → total function comp : G1 → G1 → G1 with every axiom stated on composable pairs; reason: values off the pullback are never constrained or used.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, pp. 13–15, §5 (S1, S2), p. 15 '– completing the proof that S = (S0, S1, S2) is a 2-functor.'

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §5, p. 15: `S = (S₀, S₁, S₂) : X-Mod → 2-Grp` is a 2-functor. -/
theorem S_isTwoFunctor : IsTwoFunctor S.{u} := by sorry

end StrictTwoGroups.TwoEquiv
