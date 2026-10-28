-- Prove2me | Theorems.Thm_StrictTwoGroups_TwoEquiv_proposition_comp_formula
-- name    : StrictTwoGroups.TwoEquiv.proposition_comp_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:52.920171+00:00
-- url     : https://prove2.me/theorems/5143debd-4d9b-4359-b6c8-9d1fce45f617
-- title:
--   §2, p. 6, Proposition (9) — the composition of a strict 2-group is a ∘ b = a·i(s a)⁻¹·b
-- statement:
--   Let $\mathcal G=(G_0,G_1,s,t,i,\circ)$ be a strict 2-group. Then the composition is determined by the group structure and the maps $s,t,i$: for all $a,b\in G_1$ with $s a=t b$,
--   $$a\circ b=a\;i(s a)^{-1}\;b .$$
--   In particular, if a composition satisfying the axioms of an internal category in groups exists, it is unique.
--
--   This is the reason why a strict 2-group is determined by its source, target and identity maps; it is used to compute every composition in §§4–6.
--
--   **Formalization Note** The composition is a total function `comp` whose axioms hold on composable pairs; the conclusion is stated on composable pairs only.
--
--   Differences from the source:
--   - encoding: composition $\circ:G_1\,{}_s\!\times_t G_1\to G_1$ → total function `comp` with the formula asserted for $s a=t b$; reason: the paper's map is defined only on composable pairs, and no other value is constrained or used.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 6, §2 Proposition (derivation (9))

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_StrictTwoGroup

namespace StrictTwoGroups.TwoEquiv

universe u

/-- §2, p. 6, Proposition (derivation (9)): in a strict 2-group the composition of a composable
pair is determined by `s`, `t`, `i` as `a ∘ b = a · i(s a)⁻¹ · b`. -/
theorem proposition_comp_formula (G : StrictTwoGroup.{u}) (hG : IsStrictTwoGroup G)
    (a b : G.G1) (hab : G.s a = G.t b) :
    G.comp a b = a * (G.i (G.s a))⁻¹ * b := by sorry

end StrictTwoGroups.TwoEquiv
