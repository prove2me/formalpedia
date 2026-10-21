-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_rational_weights_schur_identity
-- name    : QAlgorithms.Papers.Independent.Support21.P11.rational_weights_schur_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:02:44.568063+00:00
-- url     : https://prove2.me/theorems/d95d953c-2cd6-4743-8872-13160dd9c4d5
-- title:
--   Rational weight sum and its integral polynomial representative
-- statement:
--   Let $r\ge1$, let $P=\mathbb Z[u_1,\ldots,u_r]$ with independent variables, and work in its fraction field $K$. Define $\gamma_i=(2u_i-(-1)^r)\prod_{j\ne i}(u_i+u_j)/(u_i-u_j)$. Let $q_a$ be the coefficients of $\prod_i(1+u_it)/(1-u_it)$ and let $H_a\in P$ be the universal polynomials constructed by the reverse triangular recursion of Lemma 4.4. Then for every $a\ge0$,
--
--   $$\sum_{i=1}^r\gamma_iu_i^a=q_{a+1}(u)-\tfrac12(-1)^rq_a(u)+\tfrac12\delta_{a,0}=H_a(u)\quad\text{in }K.$$
--
--   Here $\delta_{a,0}$ is the Kronecker indicator and $P$ is mapped canonically into $K$. The last equality retains an explicit integral polynomial representative of the rational sum. This is the cited background identity from [3], Lemma 3.5, together with the paper's integral identification.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 5, §3, equation (3.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Equation (3.5), PDF p.5, cited from [3], Lemma 3.5. Independent variables
live in the fraction field of Z[u]; the actual integral representative is retained.
The printed eta sum's i/j mismatch is read as sum over j, consistently with (3.4). -/
theorem rational_weights_schur_identity (r : ℕ) (hr : 1 ≤ r) (a : ℕ) :
    let P := MvPolynomial (Fin r) ℤ
    let K := FractionRing P
    let u : Fin r → K := fun i => algebraMap P K (MvPolynomial.X i)
    (∑ i : Fin r, weightGamma u i * u i ^ a) = schurEta u a ∧
      algebraMap P K (universalH r a) = (∑ i : Fin r, weightGamma u i * u i ^ a) := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
