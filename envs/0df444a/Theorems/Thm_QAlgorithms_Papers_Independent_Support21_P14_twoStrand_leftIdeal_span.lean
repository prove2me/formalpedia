-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_twoStrand_leftIdeal_span
-- name    : QAlgorithms.Papers.Independent.Support21.P14.twoStrand_leftIdeal_span
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:27:56.262164+00:00
-- url     : https://prove2.me/theorems/fde091af-7bd7-4896-91c8-7b61206be5a5
-- title:
--   The two-strand left ideal is spanned by the affine orbit
-- statement:
--   Let $r\ge1$, and let $S$ be a commutative unital ground ring with units $\rho,q,\delta_0,u_1,\ldots,u_r$, parameters $\delta_a\in S$ for $a\ge0$, and
--   $$\rho^{-1}-\rho=(q^{-1}-q)(\delta_0-1).$$
--   Write $W_n=W_{n,S,r}(u_1,\ldots,u_r)$ for the cyclotomic BMW algebra of Definitions 2.1 and 2.8, with affine generator $y_1$ and tangle generators $e_i$.
--
--   With $e=e_1\in W_2$, the principal left ideal is exactly
--   $$W_2e=\operatorname{span}_S\{y_1^j e:0\le j<r\}.$$
--   There is no admissibility or linear-independence assumption. This supplies the spanning family used in the admissibility criteria.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 16, Lemma 3.1: two-strand left ideal spanning

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Lemma 3.1, PDF p.16. Equality of S-submodules, with no admissibility
or independence added. The left-hand side is the principal left ideal. -/
theorem twoStrand_leftIdeal_span {S : Type*} [CommRing S] {r : ℕ}
    (P : GroundParameters S r) :
    Submodule.span S {z : BMW P 2 | ∃ a : BMW P 2, z = a * bmwE P 2 0} =
      Submodule.span S (Set.range (twoStrandFamily P)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
