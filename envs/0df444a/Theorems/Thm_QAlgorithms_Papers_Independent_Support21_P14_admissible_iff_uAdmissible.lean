-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_admissible_iff_uAdmissible
-- name    : QAlgorithms.Papers.Independent.Support21.P14.admissible_iff_uAdmissible
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:30:30.52799+00:00
-- url     : https://prove2.me/theorems/c81aa797-34a6-4eaf-9860-d18e03ed3ac8
-- title:
--   Admissibility and u-admissibility over an integral domain
-- statement:
--   Let $r\ge1$, and let $S$ be a commutative unital ground ring with units $\rho,q,\delta_0,u_1,\ldots,u_r$, parameters $\delta_a\in S$ for $a\ge0$, and
--   $$\rho^{-1}-\rho=(q^{-1}-q)(\delta_0-1).$$
--   Write $W_n=W_{n,S,r}(u_1,\ldots,u_r)$ for the cyclotomic BMW algebra of Definitions 2.1 and 2.8, with affine generator $y_1$ and tangle generators $e_i$.
--
--   Weak admissibility means $\sum_{k=0}^r a_k\delta_{k+b}=0$ for every $b\in\mathbb Z$, where $\prod_{i=1}^r(t-u_i)=\sum_{k=0}^r a_kt^k$ and the negative-index parameters are constructed by Lemma 2.5's recursion.
--
--   Suppose $S$ is an integral domain. Admissibility means weak admissibility and independence of $(y_1^je_1)_{0\le j<r}$ together with nonzero, regular $q-q^{-1}$. U-admissibility means the same weak-admissibility and independence condition together with $q-q^{-1}\ne0$, distinct $u_i$, and $u_i u_j\ne1$ for all pairs. Then
--   $$S\text{ is u-admissible}\quad\Longleftrightarrow\quad S\text{ is admissible},\quad (u_i)_i\text{ are distinct},\quad u_i u_j\ne1\text{ for all }i,j.$$
--   The diagonal product exclusion is included. This identifies precisely the extra parameter separation in u-admissibility.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 23, Corollary 3.12: admissibility versus u-admissibility

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Corollary 3.12, PDF p.23. The all-pairs exclusion includes i=j. -/
theorem admissible_iff_uAdmissible {S : Type*} [CommRing S] [IsDomain S]
    {r : ℕ} (P : GroundParameters S r) :
    UAdmissible P ↔ BMWAdmissible P ∧ Function.Injective (fun j => (P.u j : S)) ∧
      (∀ i j, (P.u i : S) * ↑(P.u j) ≠ 1) := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
