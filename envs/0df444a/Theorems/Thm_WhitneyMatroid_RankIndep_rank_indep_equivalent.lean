-- Prove2me | Theorems.Thm_WhitneyMatroid_RankIndep_rank_indep_equivalent
-- name    : WhitneyMatroid.RankIndep.rank_indep_equivalent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:05:03.661814+00:00
-- url     : https://prove2.me/theorems/c62b7f6f-f18c-41bc-bbe1-a1998435aba1
-- title:
--   §6 — the rank postulates (R) and the independence postulates (I) are equivalent
-- statement:
--   Let $M$ be a finite set of elements and $\rho(N)$ the number of elements of a subset $N$.
--
--   1. If $r$ is a rank function satisfying Whitney's postulates (R₁), (R₂), (R₃), then the sets $N$ with $\rho(N) = r(N)$ satisfy the independence postulates (I₁), (I₂), the empty set is among them, and for every subset $N$, $r(N)$ equals the number of elements in a largest such set contained in $N$.
--   2. If a predicate "independent" on the subsets of $M$ satisfies (I₁), (I₂) and the empty set is independent, then
--   $$r(N) = \max\{\rho(I) : I \subseteq N,\ I \text{ independent}\}$$
--   satisfies (R₁), (R₂), (R₃), and a set $N$ is independent if and only if $\rho(N) = r(N)$.
--
--   In Whitney's words: either set of postulates (R) or (I) can be deduced from the other, and the definitions of the rank and of the independence of any subset agree under the two systems; hence the two systems are equivalent. This is the first of the cryptomorphisms of matroid theory, and it lets one pass freely between the rank and the independent sets of a matroid.
--
--   **Formalization Note** The paper takes for granted that the empty set is independent in system (I). Without it, (I₁) and (I₂) also hold for the predicate that declares no set independent; there the largest independent subset does not exist and the round trip fails. The hypothesis "$\emptyset$ is independent" is therefore stated explicitly in part 2; in part 1 it is proved. Postulate (I₂) is Whitney's form, in which $N'$ has exactly one element more than $N$. The agreement of the definitions is stated as equality of functions: the rank recovered from the independent sets of $r$ is $r$ itself, and the independent sets recovered from the rank of an independence system are the original ones.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 514, §6 (last paragraph)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankIndep

/-- §6, last paragraph (p. 514). The rank postulates (R) and the independence postulates (I)
are equivalent: each system yields the other, and the rank and the independence of every
subset agree under the two systems. The empty set is assumed independent in (I), as the
paper does tacitly. -/
theorem rank_indep_equivalent {α : Type*} [Fintype α] [DecidableEq α] :
    (∀ r : Finset α → ℤ, IsRankSystem r →
      IsIndepSystem (indepOfRank r) ∧ indepOfRank r ∅ ∧
        rankOfIndep (indepOfRank r) = r) ∧
    (∀ Indep : Finset α → Prop, IsIndepSystem Indep → Indep ∅ →
      IsRankSystem (rankOfIndep Indep) ∧ indepOfRank (rankOfIndep Indep) = Indep) := by sorry

end WhitneyMatroid.RankIndep
