-- Prove2me | Theorems.Thm_SP4FiniteGradedComplex_actual_row_rank_parity
-- name    : SP4FiniteGradedComplex.actual_row_rank_parity
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T04:03:11.363307+00:00
-- url     : https://prove2.me/theorems/de952850-0898-4346-ba33-4432a77b9d8a
-- title:
--   Even actual row-rank sum under explicit common-normalization identities
-- statement:
--   This is a conditional algebraic parity theorem for actual row complexes. The central-row identity, every column identity, and the equality of normalized total profiles are explicit hypotheses. They are not obtained here from constructed common coarsenings or from Floer theory.
--
--   Let $K$ be a field, and let $I,J,T$ be finite sets. For each $i\in I$, let $A_i^+$ and $A_i^-$ be finite permutation-indexed graded complexes of finite-dimensional $K$-vector spaces indexed by $T$: their actual differential blocks square to zero, and each nonzero block lowers the integer grade by one. Write $P_i^\pm$ for their chain-dimension Laurent polynomials, $H_i^\pm$ for their quotient-homology dimension polynomials, and $D_i^\pm$ for their total differentials.
--
--   Let $X_{0j},X_{ij}^\pm,U_0,U_i^\pm,G_j$ be integer Laurent polynomials, let $f$ be a permutation of $J$, let $k:I\times J\to\mathbb Z$ and $\ell:I\to\mathbb Z$, and let $\lambda,\mu\in\mathbb Z$. Put $V=1+q^{-1}$. Assume the following identities.
--
--   The positive auxiliary cell polynomials have zero Euler evaluation, and the opposite cell and target polynomials are related by even shifts:
--
--   $$
--   X_{ij}^+(-1)=0,\qquad
--   X_{i,f(j)}^-=q^{2k(i,j)}X_{ij}^+,\qquad
--   U_i^-=q^{2\ell(i)}U_i^+.
--   $$
--
--   The sums of auxiliary cells give the actual row chain polynomials, and the prescribed row profiles give the actual quotient-homology polynomials:
--
--   $$
--   P_i^+=\sum_jX_{ij}^+,\qquad P_i^-=\sum_jX_{ij}^-,
--   \qquad H_i^\pm=Vq^\lambda U_i^\pm.
--   $$
--
--   The central and column polynomial identities are assumed explicitly:
--
--   $$
--   \sum_jX_{0j}=Vq^\lambda U_0,\qquad
--   X_{0j}+\sum_iX_{ij}^++\sum_iX_{ij}^-=Vq^\mu G_j.
--   $$
--
--   Finally assume the Euler normalizations and equality of normalized total profiles:
--
--   $$
--   U_0(-1)+\sum_iU_i^+(-1)+\sum_iU_i^-(-1)=1,\qquad
--   \sum_jG_j(-1)=1,\qquad Vq^\lambda=Vq^\mu.
--   $$
--
--   Then
--
--   $$
--   \lambda=\mu,\qquad
--   \sum_i\operatorname{rank}_K D_i^+\equiv0\pmod2.
--   $$
--
--   The rank sum is the sum of ranks of actual linear endomorphisms, not an assumed correction coefficient. This connects the Laurent normalization argument to genuine row complexes. It remains a necessary condition under the displayed algebraic hypotheses; it constructs neither shared row/column geometry nor a topological realization.
--
--   **Formalization Note.** The parity assertion uses the integer casts of natural-number dimensions. Each row may have its own index permutation and integer grading, including repeated grades. The auxiliary cell polynomials need not individually be proved to be dimensions of subquotients: only their displayed relation to actual row chain polynomials is assumed. No claim that the central or column identities follow from actual saturated coarsenings, and no smooth four-dimensional Poincaré conclusion, is included.
-- source:
--   Local research note outputs/cycle18_structural_primary_proof.md, Sections 1–3: actual differential rank polynomials, opposite correction Euler values, and normalized parity. This theorem connects the actual finite row-complex rank-polynomial result to the existing Laurent polynomial normalization theorem. Central-row, column and normalized-total-profile identities remain explicit hypotheses; no constructed common coarsening or Floer interpretation is asserted. Primary source SHA-256 68da60b83072393fd9491dae22acb095ffce76a18a1285658417457df46188e4.

import Theorems.Thm_SP4FiniteGradedComplex_rank_polynomial
import Theorems.Thm_SP4GradedLaurent_common_normalization_parity

set_option autoImplicit false
open scoped BigOperators
open SP4FiniteGradedComplex SP4GradedLaurent

theorem SP4FiniteGradedComplex.actual_row_rank_parity {K : Type*} [Field K]
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    {Cp Cm : ι → τ → Type*}
    [∀ i j, AddCommGroup (Cp i j)] [∀ i j, Module K (Cp i j)]
    [∀ i j, FiniteDimensional K (Cp i j)]
    [∀ i j, AddCommGroup (Cm i j)] [∀ i j, Module K (Cm i j)]
    [∀ i j, FiniteDimensional K (Cm i j)]
    (Ap : ∀ i, Data K τ (Cp i)) (Am : ∀ i, Data K τ (Cm i))
    (flip : κ ≃ κ) (k : ι → κ → ℤ) (l : ι → ℤ)
    (X0 : κ → GradedPolynomial) (Xp Xm : ι → κ → GradedPolynomial)
    (U0 : GradedPolynomial) (Up Um : ι → GradedPolynomial)
    (G : κ → GradedPolynomial) (lam mu : ℤ)
    (hcell : ∀ i j, euler (Xp i j) = 0)
    (hconj : ∀ i j, Xm i (flip j) = shift (2 * k i j) (Xp i j))
    (htarget : ∀ i, Um i = shift (2 * l i) (Up i))
    (hchainp : ∀ i, chainPolynomial (Ap i) = ∑ j, Xp i j)
    (hchainm : ∀ i, chainPolynomial (Am i) = ∑ j, Xm i j)
    (hhomologyp : ∀ i, homologyPolynomial (Ap i) = tensorV (shift lam (Up i)))
    (hhomologym : ∀ i, homologyPolynomial (Am i) = tensorV (shift lam (Um i)))
    (hrow0 : ∑ j, X0 j = tensorV (shift lam U0))
    (hcolumn : ∀ j, X0 j + ∑ i, Xp i j + ∑ i, Xm i j = tensorV (shift mu (G j)))
    (hU : euler U0 + ∑ i, euler (Up i) + ∑ i, euler (Um i) = 1)
    (hG : ∑ j, euler (G j) = 1)
    (hnorm : tensorV (Finsupp.single lam 1) = tensorV (Finsupp.single mu 1)) :
    lam = mu ∧ Even (∑ i, (Module.finrank K (LinearMap.range (totalD (Ap i))) : ℤ)) := by sorry
