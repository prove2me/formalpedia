-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_zeta_isTwoNatIso
-- name    : StrictTwoGroups.TwoEquiv.zeta_isTwoNatIso
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:37:26.367668+00:00
-- url     : https://prove2.me/theorems/197cb895-0135-4cc2-a5ad-6e589619e05b
-- title:
--   §6, p. 16 — ζ_χ = (id, π₁|ker π₂) is a 2-natural isomorphism TS ⇒ id_{X-Mod}
-- statement:
--   For a crossed module $\chi=(G,H,\tau,\alpha)$ let $\zeta_\chi=(\mathrm{id}_G,\pi_1|_{\ker\pi_2}):TS\chi\to\chi$, where $TS\chi=(G,\ker\pi_2,\tau\pi_1|_{\ker\pi_2},\mathrm{Ad}_{i_2})$ and $\ker\pi_2\subseteq H\rtimes G$. Then $\zeta$ is a 2-natural isomorphism
--   $$\zeta:TS\Longrightarrow\mathrm{id}_{X\text{-}\mathit{Mod}}:$$
--   each $\zeta_\chi$ is an isomorphism of crossed modules, $\zeta_{\chi'}\circ TS(\gamma,\delta)=(\gamma,\delta)\circ\zeta_\chi$ for every morphism, and for every 2-morphism $\eta$ the whiskered composites agree: $i\zeta_{\chi'}\circ TS(\eta)=\eta\circ i\zeta_\chi$ (diagram (7)).
--
--   Together with $\xi$, this is half of the 2-equivalence of §6.
--
--   **Formalization Note** `IsTwoNatIso (S.comp T) (Raw2Functor.id xMod) zeta`: `S.comp T` is "$S$, then $T$", the paper's $TS$. An isomorphism is a lawful 1-cell with a lawful two-sided inverse.
--
--   Differences from the source:
--   - encoding: 2-categories given by their cells, compositions and identities; morphisms and 2-morphisms are group morphisms / maps with their source and target → raw data (Raw2Cat) with lawfulness predicates IsOb, Is1, Is2, every law quantified over lawful cells only; 2-cells typed by their objects with the boundary 1-cells as explicit arguments; cells are plain functions and "is a group morphism" is a clause of Is1 / Is2; reason: changes no instance: the lawful objects, 1-cells and 2-cells are exactly the paper's, and nothing is asserted about the others.
--   - encoding: applicative composition (γ′ ∘ γ, η′ ∘ η, E ∘ F) → diagrammatic comp1 f g, vcomp, hcomp and Raw2Functor.comp ("first, then second"); reason: notation only; every composite is the same map as on the page.
--   - encoding: composition ∘ : G1 s×t G1 → G1 of a strict 2-group → total function comp : G1 → G1 → G1 with every axiom stated on composable pairs; reason: values off the pullback are never constrained or used.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 16, §6 (ζ_χ and diagram (7))

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_RoundTrip

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §6, p. 16: the 1-cells `ζ_χ = (id, π₁|_{ker π₂}) : TSχ → χ` form a 2-natural isomorphism
`ζ : TS ⇒ id_{X-Mod}`. -/
theorem zeta_isTwoNatIso : IsTwoNatIso (S.comp T) (Raw2Functor.id xMod.{u}) zeta := by sorry

end StrictTwoGroups.TwoEquiv
