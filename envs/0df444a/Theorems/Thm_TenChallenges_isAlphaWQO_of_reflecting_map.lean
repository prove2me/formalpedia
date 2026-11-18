-- Prove2me | Theorems.Thm_TenChallenges_isAlphaWQO_of_reflecting_map
-- name    : TenChallenges.isAlphaWQO_of_reflecting_map
-- status  : Proved
-- author  : @Davide
-- created : 2026-11-17T10:46:11.197188+00:00
-- url     : https://prove2.me/theorems/a3a9be59-e811-43ae-8ba0-9b2febe527eb
-- title:
--   $\alpha$-well-quasi-ordering pulls back along order-reflecting maps
-- statement:
--   Let $(P,\le_P)$ and $(Q,\le_Q)$ be sets with binary relations, and let $e\colon P\to Q$ be a map that **reflects** the order:
--
--   $$e(x)\le_Q e(y)\ \Longrightarrow\ x\le_P y\qquad(x,y\in P).$$
--
--   Then for every ordinal $\alpha$, if $(Q,\le_Q)$ is $\alpha$-well-quasi-ordered, so is $(P,\le_P)$. Here $\alpha$-WQO means that level $\alpha$ of the Nash-Williams cumulative hierarchy $V^*_\alpha$ (nonempty subsets at successor levels, disjoint unions at limit levels) is well-quasi-ordered under the game relation $\le^*$, as in the definition `IsAlphaWQO`.
--
--   The case $\alpha=0$ is the familiar fact that a well-quasi-order restricts to subsets. In general, $e$ induces a map $V^*_\alpha(P)\to V^*_\alpha(Q)$ (apply $e$ at level $0$, take images at successor levels, keep the tag at limit levels), and this map reflects $\le^*$. A bad sequence in $V^*_\alpha(P)$ would therefore push forward to a bad sequence in $V^*_\alpha(Q)$. In particular, applied to the inclusion of planar graphs into all finite graphs, it shows that whenever finite graphs are $\alpha$-WQO under minors, so are finite planar graphs.
-- source:
--   Standard closure property of α-WQO and BQO under substructures (e.g. Marcone, 'Foundations of bqo theory', Trans. AMS 345 (1994)). Stated for the hierarchy and game relation of the definition TenChallenges_AlphaWQO, used by Ten Challenges 06.

import Definitions.Def_TenChallenges_AlphaWQO

universe u

namespace TenChallenges
theorem isAlphaWQO_of_reflecting_map {P Q : Type u} (leP : P → P → Prop) (leQ : Q → Q → Prop)
    (e : P → Q) (he : ∀ x y, leQ (e x) (e y) → leP x y) (α : Ordinal.{u}) :
    IsAlphaWQO leQ α → IsAlphaWQO leP α := by sorry
end TenChallenges
