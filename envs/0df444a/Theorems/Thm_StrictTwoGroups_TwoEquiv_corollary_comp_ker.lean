-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_corollary_comp_ker
-- name    : StrictTwoGroups.TwoEquiv.corollary_comp_ker
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:51.743991+00:00
-- url     : https://prove2.me/theorems/ef41bc62-9305-4209-a5b5-44e85bbd0485
-- title:
--   §2, p. 6, Corollary (10) — for a ∈ ker s, a ∘ b = a·i(s a)⁻¹·b = ab
-- statement:
--   Let $\mathcal G$ be a strict 2-group, $a\in\ker s$ and $b\in G_1$ composable with $a$ ($s a=t b$, i.e. $t b=e$). Then
--   $$a\circ b=a\;i(s a)^{-1}\;b=a\,b .$$
--   On the kernel of the source map, composition is group multiplication. This is what makes the second component of $\ker s\rtimes G_0$ carry the composition in §§4–6.
--
--   **Formalization Note** The composability condition $s a=t b$ is explicit; it is implicit on the page because $a\circ b$ is only defined for composable pairs.
--
--   Differences from the source:
--   - encoding: $a\circ b$ for $a\in\ker s$ (defined only for composable pairs) → hypothesis $s a=t b$ and total `comp`; reason: the paper's composition is defined only on $G_1\,{}_s\!\times_t G_1$.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 6, §2 Corollary (10)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_StrictTwoGroup

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §2, p. 6, Corollary (10): for `a ∈ ker s` (and `b` composable with `a`),
`a ∘ b = a · i(s a)⁻¹ · b = a b`. -/
theorem corollary_comp_ker (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (ha : G.s a = 1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b ∧ G.comp a b = a * b := by sorry

end StrictTwoGroups.TwoEquiv
