-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_uAdmissibility_equivalences
-- name    : QAlgorithms.Papers.Independent.Support21.P14.uAdmissibility_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:29:53.15237+00:00
-- url     : https://prove2.me/theorems/c943c1ee-adbb-4994-b082-812f6c3c8656
-- title:
--   Three equivalent u-admissibility conditions over the ground ring
-- statement:
--   Let $r\ge1$, and let $S$ be a commutative unital ground ring with units $\rho,q,\delta_0,u_1,\ldots,u_r$, parameters $\delta_a\in S$ for $a\ge0$, and
--   $$\rho^{-1}-\rho=(q^{-1}-q)(\delta_0-1).$$
--   Write $W_n=W_{n,S,r}(u_1,\ldots,u_r)$ for the cyclotomic BMW algebra of Definitions 2.1 and 2.8, with affine generator $y_1$ and tangle generators $e_i$.
--
--   Suppose $S$ is an integral domain, $q-q^{-1}\ne0$, the $u_j$ are distinct, and $u_i u_j\ne1$ for every pair. In $F=\operatorname{Frac}(S)$, Put $C_{ij}=(1-u_i u_j)^{-1}$ and $P_j=\prod_{\ell\ne j}(u_\ell u_j-1)/(u_j-u_\ell)$.
--
--   Define
--   $$\gamma_j=P_j\left(\frac{1-u_j^2}{\rho(q^{-1}-q)}\prod_{\ell\ne j}u_\ell+\begin{cases}1,&r\text{ odd},\\-u_j,&r\text{ even}.\end{cases}\right).$$
--
--   Weak admissibility means $\sum_{k=0}^r a_k\delta_{k+b}=0$ for every $b\in\mathbb Z$, where $\prod_{i=1}^r(t-u_i)=\sum_{k=0}^r a_kt^k$ and the negative-index parameters are constructed by Lemma 2.5's recursion.
--
--   The following are equivalent:
--   1. $S$ is weakly admissible and $(y_1^je_1)_{0\le j<r}$ is $S$-linearly independent.
--   2. After embedding $S$ into $F$,
--   $$\delta_a=\sum_{j=1}^r\gamma_j u_j^a\quad\text{for all }a\ge0.$$
--   3. $S$ is weakly admissible and $W_2$ has a module with $S$-basis $(v_0,y_1v_0,\ldots,y_1^{r-1}v_0)$ and $e_1v_0=\delta_0v_0$.
--
--   This compares the module-theoretic and explicit moment forms of u-admissibility. Individual $\gamma_j$ are only elements of $F$; the module in condition 3 is over $S$.
--
--   **Formalization Note** The basis module is represented on $S^r$ by transport along the specified basis.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 19, Theorem 3.10: u-admissibility equivalences

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Theorem 3.10, PDF pp.19--20. All three equivalences, with the moments
in Frac(S) and an actual orbit-basis module over S. -/
theorem uAdmissibility_equivalences {S : Type*} [CommRing S] [IsDomain S]
    {r : ℕ} (P : GroundParameters S r)
    (hq : (↑P.q - ↑P.q⁻¹ : S) ≠ 0)
    (hu : Function.Injective (fun j => (P.u j : S)))
    (hprod : ∀ i j, (P.u i : S) * ↑(P.u j) ≠ 1) :
    ((WeakAdmissible P ∧ LinearIndependent S (twoStrandFamily P)) ↔ FractionFieldMoments P) ∧
    (FractionFieldMoments P ↔ (WeakAdmissible P ∧ HasCyclicBasisModule P)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
