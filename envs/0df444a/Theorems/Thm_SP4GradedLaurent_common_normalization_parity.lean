-- Prove2me | Theorems.Thm_SP4GradedLaurent_common_normalization_parity
-- name    : SP4GradedLaurent.common_normalization_parity
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T01:57:27.507685+00:00
-- url     : https://prove2.me/theorems/b94477c7-68b8-47eb-b93d-323511c37745
-- title:
--   Common-normalization parity obstruction (polynomial layer)
-- statement:
--   Let $I,J$ be finite index sets, let $\sigma:J\to J$ be a permutation, and let all polynomials below be finite Laurent polynomials with integer coefficients. Write
--
--   $$
--   V=1+q^{-1},\qquad \chi(P)=P(-1).
--   $$
--
--   The source data consist of a central row $X^0_j$ and paired rows $X^+_{ij},X^-_{ij}$. The target and correction data are $U_0,U_i^+,U_i^-,Q_i^+,Q_i^-$, and the column targets are $G_j$. Let $\lambda,\mu$, $k_{ij}$, and $\ell_i$ be integers.
--
--   Assume cellwise Euler zero and even-shift conjugation:
--
--   $$
--   \chi(X^+_{ij})=0,\qquad
--   X^-_{i,\sigma(j)}=q^{2k_{ij}}X^+_{ij},\qquad
--   U_i^-=q^{2\ell_i}U_i^+.
--   $$
--
--   Assume the following exact identities of Laurent polynomials, with the same shift $\lambda$ in every row and the same shift $\mu$ in every column:
--
--   $$
--   \begin{aligned}
--   \sum_jX^0_j&=q^\lambda VU_0,\\
--   \sum_jX^+_{ij}&=q^\lambda VU_i^+ + VQ_i^+,\\
--   \sum_jX^-_{ij}&=q^\lambda VU_i^- + VQ_i^-,\\
--   X^0_j+\sum_iX^+_{ij}+\sum_iX^-_{ij}&=q^\mu VG_j.
--   \end{aligned}
--   $$
--
--   Finally assume the target Euler normalizations and equality of the two translated adjacent-degree total profiles:
--
--   $$
--   \chi(U_0)+\sum_i\chi(U_i^+)+\sum_i\chi(U_i^-)=1,
--   \qquad \sum_j\chi(G_j)=1,
--   \qquad q^\lambda V=q^\mu V.
--   $$
--
--   Then
--
--   $$
--   \lambda=\mu
--   \qquad\text{and}\qquad
--   \sum_{i\in I}Q_i^+(1)\in2\mathbb Z.
--   $$
--
--   This is the polynomial layer of a common-normalization obstruction: an odd total correction coefficient sum is incompatible with these identities. The polynomials may have arbitrary integer coefficients. Interpreting correction coefficients as ranks of actual differential blocks requires a separate graded-complex argument; no such rank interpretation, Floer-theoretic realization, or geometric exclusion is asserted here.
-- source:
--   Local research notes, Cycle 18, A basis-free parity obstruction from saturation and common normalization, Sections 2–3, equations (1)–(4); independent critical audit Sections 1–3. This formalization extracts only their integer Laurent-polynomial implication. The actual graded-complex rank-nullity bridge and applications to named source tables are not included. Primary note: cycle18_structural_primary_proof.md, SHA-256 68da60b83072393fd9491dae22acb095ffce76a18a1285658417457df46188e4.

import Definitions.Def_SP4GradedLaurent

set_option autoImplicit false

open scoped BigOperators
open SP4GradedLaurent

theorem SP4GradedLaurent.common_normalization_parity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (flip : κ ≃ κ) (k : ι → κ → ℤ) (l : ι → ℤ)
    (X0 : κ → GradedPolynomial) (Xp Xm : ι → κ → GradedPolynomial)
    (U0 : GradedPolynomial) (Up Um Qp Qm : ι → GradedPolynomial)
    (G : κ → GradedPolynomial) (lam mu : ℤ)
    (hcell : ∀ i j, euler (Xp i j) = 0)
    (hconj : ∀ i j, Xm i (flip j) = shift (2 * k i j) (Xp i j))
    (htarget : ∀ i, Um i = shift (2 * l i) (Up i))
    (hrow0 : ∑ j, X0 j = tensorV (shift lam U0))
    (hrowp : ∀ i, ∑ j, Xp i j = tensorV (shift lam (Up i)) + tensorV (Qp i))
    (hrowm : ∀ i, ∑ j, Xm i j = tensorV (shift lam (Um i)) + tensorV (Qm i))
    (hcolumn : ∀ j, X0 j + ∑ i, Xp i j + ∑ i, Xm i j = tensorV (shift mu (G j)))
    (hU : euler U0 + ∑ i, euler (Up i) + ∑ i, euler (Um i) = 1)
    (hG : ∑ j, euler (G j) = 1)
    (hnorm : tensorV (Finsupp.single lam 1) = tensorV (Finsupp.single mu 1)) :
    lam = mu ∧ Even (∑ i, mass (Qp i)) := by sorry
