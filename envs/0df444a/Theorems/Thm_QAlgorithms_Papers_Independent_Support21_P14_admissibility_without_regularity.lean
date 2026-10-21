-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_admissibility_without_regularity
-- name    : QAlgorithms.Papers.Independent.Support21.P14.admissibility_without_regularity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:28:20.829457+00:00
-- url     : https://prove2.me/theorems/924fd7c0-3090-4967-b814-41e91448dd19
-- title:
--   Three equivalent admissibility conditions without regularity
-- statement:
--   Let $r\ge1$, and let $S$ be a commutative unital ground ring with units $\rho,q,\delta_0,u_1,\ldots,u_r$, parameters $\delta_a\in S$ for $a\ge0$, and
--   $$\rho^{-1}-\rho=(q^{-1}-q)(\delta_0-1).$$
--   Write $W_n=W_{n,S,r}(u_1,\ldots,u_r)$ for the cyclotomic BMW algebra of Definitions 2.1 and 2.8, with affine generator $y_1$ and tangle generators $e_i$.
--
--   Weak admissibility means $\sum_{k=0}^r a_k\delta_{k+b}=0$ for every $b\in\mathbb Z$, where $\prod_{i=1}^r(t-u_i)=\sum_{k=0}^r a_kt^k$ and the negative-index parameters are constructed by Lemma 2.5's recursion.
--
--   Assume weak admissibility. The following are equivalent: the family $(y_1^je_1)_{0\le j<r}$ is $S$-linearly independent; the two parameter relations below hold; and $W_2$ has a cyclic module $M$ with $S$-basis $(v_0,y_1v_0,\ldots,y_1^{r-1}v_0)$ satisfying $e_1v_0=\delta_0v_0$. The relations, with $a_j$ as above, are
--   $$\rho(a_\ell-a_{r-\ell}/a_0)+(q-q^{-1})\left[\sum_{j=1}^{r-\ell}a_{j+\ell}\delta_j-\sum_{j=\max(\ell+1,\lceil r/2\rceil)}^{\lfloor(\ell+r)/2\rfloor}a_{2j-\ell}+\sum_{j=\lceil\ell/2\rceil}^{\min(\ell,\lceil r/2\rceil-1)}a_{2j-\ell}\right]=0\quad(1\le\ell<r),$$
--   $$\rho^{-1}a_0-\rho a_0^{-1}=\begin{cases}0,&r\text{ odd},\\q-q^{-1},&r\text{ even}.\end{cases}$$
--   Empty sums are zero, and $q-q^{-1}$ is allowed to be zero or a zero divisor. This is the admissibility equivalence in the absence of a regularity assumption.
--
--   **Formalization Note** A module with the displayed basis is transported to $S^r$, where its full unital BMW action is retained as an algebra homomorphism into its endomorphism algebra. This is equivalent to the abstract-module assertion.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 17, Corollary 3.4: admissibility equivalence without regularity

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Corollary 3.4, PDF p.17. All three conditions; q=q inverse is allowed.
The orbit-basis module is over S, not over a fraction field. -/
theorem admissibility_without_regularity {S : Type*} [CommRing S] {r : ℕ}
    (P : GroundParameters S r) (hweak : WeakAdmissible P) :
    (LinearIndependent S (twoStrandFamily P) ↔ WilcoxYuRelations P) ∧
    (WilcoxYuRelations P ↔ HasCyclicBasisModule P) := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
