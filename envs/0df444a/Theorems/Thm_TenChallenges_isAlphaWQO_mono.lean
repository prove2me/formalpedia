-- Prove2me | Theorems.Thm_TenChallenges_isAlphaWQO_mono
-- name    : TenChallenges.isAlphaWQO_mono
-- status  : Proved
-- author  : @Davide
-- created : 2026-11-17T15:26:37.747067+00:00
-- url     : https://prove2.me/theorems/8925b810-9e0b-4443-add2-b0fb526df437
-- title:
--   $\alpha$-well-quasi-ordering is monotone in $\alpha$
-- statement:
--   Let $(Q,\le)$ be a set with a binary relation and let $\beta\le\alpha$ be ordinals. If $(Q,\le)$ is $\alpha$-well-quasi-ordered, then it is $\beta$-well-quasi-ordered:
--
--   $$\beta\le\alpha\ \text{ and }\ (V^*_\alpha(Q),\le^*)\ \text{WQO}\ \Longrightarrow\ (V^*_\beta(Q),\le^*)\ \text{WQO}.$$
--
--   Here $V^*_\alpha(Q)$ is the Nash-Williams cumulative hierarchy (nonempty subsets at successor levels, disjoint unions at limit levels) with the game relation $\le^*$, as in the definition `IsAlphaWQO`.
--
--   So the $\alpha$-WQO properties form a hierarchy of strengthenings of well-quasi-ordering ($0$-WQO), with better-quasi-ordering at the top. For the minor order this means, for instance, that each rung of Challenge 6 implies the lower rungs of the same parity; in particular $\mathrm{WQO}(2)$ implies $\mathrm{WQO}(0)$.
-- source:
--   Standard property of the α-WQO hierarchy (Marcone, 'Foundations of bqo theory', Trans. AMS 345 (1994)); stated for the hierarchy and game relation of the definition TenChallenges_AlphaWQO, used by Ten Challenges 06.

import Definitions.Def_TenChallenges_AlphaWQO

universe u

namespace TenChallenges
theorem isAlphaWQO_mono {Q : Type u} (le : Q → Q → Prop) {α β : Ordinal.{u}} (h : β ≤ α) :
    IsAlphaWQO le α → IsAlphaWQO le β := by sorry
end TenChallenges
