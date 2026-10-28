-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_toTwoGrp_isStrictTwoGroup
-- name    : StrictTwoGroups.TwoEquiv.toTwoGrp_isStrictTwoGroup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:22.644977+00:00
-- url     : https://prove2.me/theorems/3ca798b4-d89f-4515-be7d-a83189b3a4fc
-- title:
--   §5, pp. 12–13 — S₀(χ) = (G, H ⋊ G, s, t, i) is a strict 2-group
-- statement:
--   Let $\chi=(G,H,\tau,\alpha)$ be a crossed module and let $H\rtimes G$ be the semidirect product with $(h,g)(h',g')=(h\,\alpha(g,h'),gg')$. With
--   $$s(h,g)=g,\qquad t(h,g)=\tau h\,g,\qquad i(g)=(e,g),\qquad (j,\tau h\,g)\circ(h,g)=(jh,g),$$
--   the tuple $S_0(\chi)=(G,H\rtimes G,s,t,i,\circ)$ is a strict 2-group: the composition is a group morphism on composable pairs (interchange law), and the source, target, unit and associativity axioms hold.
--
--   This is the object part of the 2-functor $S:X\text{-}\mathit{Mod}\to2\text{-}\mathit{Grp}$. The same construction, in a different encoding of strict 2-groups (with an extra arrow-inverse datum), is the proved platform theorem `QAlgorithms.Papers.Independent.Renew46.P18.crossedModule_strictTwoGroup`.
--
--   **Formalization Note** That $s,t,i$ are group morphisms and $s\,i=t\,i=\mathrm{id}$ are part of the definition `toTwoGrp` ($t$ is a morphism by equivariance); the theorem asserts the remaining axioms, `IsStrictTwoGroup (toTwoGrp χ)`, under the Peiffer identity. The composition is the total map $(b,a)\mapsto(b_1a_1,a_2)$, the paper's formula on composable pairs.
--
--   Differences from the source:
--   - encoding: composition defined on composable pairs $(j,\tau h\,g)\circ(h,g)=(jh,g)$ → total map $(b,a)\mapsto(b_1a_1,a_2)$; reason: on composable pairs it is the paper's formula, and the axioms of `IsStrictTwoGroup` are stated on composable pairs only.
--   - reading: an action α : G × H → H of a crossed module → α : G →* MulAut H (an action by group automorphisms); reason: the standard meaning of a crossed module's action, and the one the paper uses: the semidirect product H ⋊ G of §5 (p. 12) and S₀'s target map being a morphism (p. 13) require it; for a mere set action H ⋊ G is not a group.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, pp. 12–13, §5 (S0)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Functors

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §5, pp. 12–13: for a crossed module `χ = (G, H, τ, α)`,
`S₀(χ) = (G, H ⋊ G, s, t, i)` with composition `(j, τ(h) g) ∘ (h, g) = (j h, g)` is a strict
2-group. -/
theorem toTwoGrp_isStrictTwoGroup (χ : CrossedModule.{u}) (hχ : IsCrossedModule χ) :
    IsStrictTwoGroup (toTwoGrp χ) := by sorry

end StrictTwoGroups.TwoEquiv
