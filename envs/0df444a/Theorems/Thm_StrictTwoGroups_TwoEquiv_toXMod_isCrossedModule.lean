-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_toXMod_isCrossedModule
-- name    : StrictTwoGroups.TwoEquiv.toXMod_isCrossedModule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:33.724663+00:00
-- url     : https://prove2.me/theorems/b491662e-0da8-4227-8d51-eebbd4d296f2
-- title:
--   §4, pp. 10–11 — T₀(G) = (G₀, ker s, t|ker s, Ad∘i) is a crossed module
-- statement:
--   Let $\mathcal G=(G_0,G_1,s,t,i,\circ)$ be a strict 2-group. Then
--   $$T_0(\mathcal G)=\bigl(G_0,\ \ker s,\ t|_{\ker s},\ \alpha(g,h)=ig\,h\,(ig)^{-1}\bigr)$$
--   is a crossed module; that is, besides the equivariance $t(ig\,h\,(ig)^{-1})=g\,t(h)\,g^{-1}$, the Peiffer identity holds: for all $h,h'\in\ker s$,
--   $$\alpha(t h,h')=h\,h'\,h^{-1}.$$
--
--   This is the object part of the 2-functor $T:2\text{-}\mathit{Grp}\to X\text{-}\mathit{Mod}$.
--
--   **Formalization Note** Equivariance is a structure field of `CrossedModule` and is proved inside the definition `toXMod` (it uses only $t\,i=\mathrm{id}$); the theorem asserts the Peiffer identity, `IsCrossedModule (toXMod G)`, for every `G` satisfying `IsStrictTwoGroup`.
--
--   Differences from the source:
--   - encoding: composition ∘ : G1 s×t G1 → G1 of a strict 2-group → total function comp : G1 → G1 → G1 with every axiom stated on composable pairs; reason: values off the pullback are never constrained or used.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, pp. 10–11, §4 (T0 and the Peiffer identity)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §4, pp. 10–11: for a strict 2-group `G`, `T₀(G) = (G₀, ker s, t|_{ker s}, Ad ∘ i)` satisfies
the Peiffer identity, so it is a crossed module. -/
theorem toXMod_isCrossedModule (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G) :
    IsCrossedModule (toXMod G) := by sorry

end StrictTwoGroups.TwoEquiv
