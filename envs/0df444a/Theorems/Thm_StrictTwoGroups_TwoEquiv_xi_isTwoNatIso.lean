-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_xi_isTwoNatIso
-- name    : StrictTwoGroups.TwoEquiv.xi_isTwoNatIso
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:37:50.971669+00:00
-- url     : https://prove2.me/theorems/cca36d27-2a9e-4fe7-b45e-3c38da1fc40c
-- title:
--   §6, p. 15 — ξ_G = (id, ϕ⁻¹) is a 2-natural isomorphism ST ⇒ id_{2-Grp} (corrected: domain STG for the printed TSG)
-- statement:
--   For a strict 2-group $\mathcal G$ let $\xi_{\mathcal G}=(\mathrm{id}_{G_0},\varphi^{-1}):ST\mathcal G\to\mathcal G$, where $ST\mathcal G=(G_0,\ker s\rtimes G_0,\dots)$ and
--   $$\varphi^{-1}(h,g)=h\,ig .$$
--   Then $\xi$ is a 2-natural isomorphism $ST\Rightarrow\mathrm{id}_{2\text{-}\mathit{Grp}}$: each $\xi_{\mathcal G}$ is an isomorphism of strict 2-groups, $\xi_{\mathcal G'}\circ ST(f)=f\circ\xi_{\mathcal G}$ for every morphism $f:\mathcal G\to\mathcal G'$, and for every 2-morphism $\vartheta:f\Rightarrow g$ the whiskered composites agree: $i\xi_{\mathcal G'}\circ ST(\vartheta)=\vartheta\circ i\xi_{\mathcal G}$ (diagram (7)).
--
--   Together with $\zeta$, this is half of the 2-equivalence of §6.
--
--   **Formalization Note** `IsTwoNatIso (T.comp S) (Raw2Functor.id twoGrp) xi`: `T.comp S` is "$T$, then $S$", the paper's $ST$. An isomorphism is a lawful 1-cell with a lawful two-sided inverse.
--
--   Differences from the source:
--   - correction: $\xi_{\mathcal G}:TS\mathcal G\to\mathcal G$ (p. 15) → $\xi_{\mathcal G}:ST\mathcal G\to\mathcal G$; reason: $TS$ is an endo-2-functor of $X\text{-}\mathit{Mod}$, so $TS\mathcal G$ is undefined for a strict 2-group $\mathcal G$; the paper's own formula $\varphi^{-1}:\ker s\rtimes G_0\to G_1$ and the heading $\xi:ST\Rightarrow\mathrm{id}_{2\text{-}\mathit{Grp}}$ fix the domain as $ST\mathcal G$.
--   - encoding: 2-categories given by their cells, compositions and identities; morphisms and 2-morphisms are group morphisms / maps with their source and target → raw data (Raw2Cat) with lawfulness predicates IsOb, Is1, Is2, every law quantified over lawful cells only; 2-cells typed by their objects with the boundary 1-cells as explicit arguments; cells are plain functions and "is a group morphism" is a clause of Is1 / Is2; reason: changes no instance: the lawful objects, 1-cells and 2-cells are exactly the paper's, and nothing is asserted about the others.
--   - encoding: applicative composition (γ′ ∘ γ, η′ ∘ η, E ∘ F) → diagrammatic comp1 f g, vcomp, hcomp and Raw2Functor.comp ("first, then second"); reason: notation only; every composite is the same map as on the page.
--   - encoding: composition ∘ : G1 s×t G1 → G1 of a strict 2-group → total function comp : G1 → G1 → G1 with every axiom stated on composable pairs; reason: values off the pullback are never constrained or used.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 15, §6 (ξ_G and diagram (7))

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_RoundTrip

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §6, p. 15: the 1-cells `ξ_G = (id, ϕ⁻¹) : STG → G` form a 2-natural isomorphism
`ξ : ST ⇒ id_{2-Grp}`. -/
theorem xi_isTwoNatIso : IsTwoNatIso (T.comp S) (Raw2Functor.id twoGrp.{u}) xi := by sorry

end StrictTwoGroups.TwoEquiv
