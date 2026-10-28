-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_T_isTwoFunctor
-- name    : StrictTwoGroups.TwoEquiv.T_isTwoFunctor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:30.48599+00:00
-- url     : https://prove2.me/theorems/aae6ec5d-eb85-4907-8483-74cb0a25c275
-- title:
--   §4, p. 12 — T = (T₀, T₁, T₂) : 2-Grp → X-Mod is a 2-functor
-- statement:
--   The assignment
--   $$T_0(\mathcal G)=(G_0,\ker s,t|_{\ker s},\mathrm{Ad}\circ i),\qquad T_1(f_0,f_1)=(f_0,f_1|_{\ker s}),\qquad T_2\vartheta=\pi_1\varphi'\vartheta:\ g\mapsto\vartheta g\;i's'(\vartheta g)^{-1}$$
--   is a 2-functor $T:2\text{-}\mathit{Grp}\to X\text{-}\mathit{Mod}$: it sends strict 2-groups to crossed modules, morphisms to morphisms and 2-morphisms to 2-morphisms, each $T_{\mathcal G,\mathcal G'}$ is a functor, and $T$ preserves horizontal composition and identities of 1-cells and 2-cells.
--
--   **Formalization Note** On lawful data `IsTwoFunctor T` asserts preservation of lawful objects, 1-cells and 2-cells, of identity 2-cells, vertical composition, horizontal composition of 1-cells and 2-cells, and of identity 1-cells and their identity 2-cells. $T_1$'s second component is written $h\mapsto\pi_1\varphi'(f_1h)$, which equals $f_1|_{\ker s}$ on every morphism of strict 2-groups.
--
--   Differences from the source:
--   - encoding: $T_1(f_0,f_1)=(f_0,f_1|_{\ker s})$ → $(f_0,\ h\mapsto f_1h\;i'(s'(f_1h))^{-1})$; reason: the restriction lands in $\ker s'$ only for lawful $(f_0,f_1)$; on every lawful 1-cell the two maps coincide, and `IsTwoFunctor` only constrains lawful 1-cells.
--   - encoding: 2-categories given by their cells, compositions and identities; morphisms and 2-morphisms are group morphisms / maps with their source and target → raw data (Raw2Cat) with lawfulness predicates IsOb, Is1, Is2, every law quantified over lawful cells only; 2-cells typed by their objects with the boundary 1-cells as explicit arguments; cells are plain functions and "is a group morphism" is a clause of Is1 / Is2; reason: changes no instance: the lawful objects, 1-cells and 2-cells are exactly the paper's, and nothing is asserted about the others.
--   - encoding: applicative composition (γ′ ∘ γ, η′ ∘ η, E ∘ F) → diagrammatic comp1 f g, vcomp, hcomp and Raw2Functor.comp ("first, then second"); reason: notation only; every composite is the same map as on the page.
--   - encoding: composition ∘ : G1 s×t G1 → G1 of a strict 2-group → total function comp : G1 → G1 → G1 with every axiom stated on composable pairs; reason: values off the pullback are never constrained or used.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 12, §4 'This completes the proof that T : 2-Grp → X-Mod is a 2-functor.'

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §4, p. 12: `T = (T₀, T₁, T₂) : 2-Grp → X-Mod` is a 2-functor. -/
theorem T_isTwoFunctor : IsTwoFunctor T.{u} := by sorry

end StrictTwoGroups.TwoEquiv
