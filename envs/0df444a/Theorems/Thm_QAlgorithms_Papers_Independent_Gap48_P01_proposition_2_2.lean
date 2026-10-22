-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_proposition_2_2
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.proposition_2_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:41:56.784327+00:00
-- url     : https://prove2.me/theorems/0baa1303-14da-4341-958f-903b7e216f6f
-- title:
--   Proposition 2.2
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   The following identities hold, with $p\in\mathbb Z$:
--   $$
--   \begin{aligned}
--   X_i^2&=1+\delta X_i-\delta\lambda e_i,\\
--   e_iX_je_i&=\lambda^{-1}e_i &&(|i-j|=1),\\
--   X_iY'_j&=Y'_jX_i,\quad e_iY'_j=Y'_je_i &&(i\ne j,\ i+1\ne j),\\
--   Y'_iY'_j&=Y'_jY'_i,\\
--   Y'_iX_iY'_ie_i&=\lambda^{-1}e_i=e_iY'_iX_iY'_i,\\
--   e_i(Y'_{i+1})^p&=e_i(Y'_i)^{-p},\quad (Y'_{i+1})^pe_i=(Y'_i)^{-p}e_i.
--   \end{aligned}
--   $$
--   These are the commutation and transport relations used in the spanning construction. The sign in the adjacent index $i\pm1$ does not denote inversion.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 6, Proposition 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Proposition 2.2, all six relations (17)--(22), PDF p.6.
The printed 'i != j or j-1' means both exclusions. The sign in (18) is
an adjacent INDEX, not an inverse. Each source generator is in range. -/
theorem proposition_2_2 :
    (∀ i, 1 ≤ i → i < n → X P n i false ^ 2 =
      1 + algebraMap R _ (skeinDelta P) * X P n i false -
        algebraMap R _ (skeinDelta P * (P.lam : R)) * E P n i) ∧
    (∀ i j, 1 ≤ i → i < n → 1 ≤ j → j < n → (i+1=j ∨ j+1=i) →
      E P n i * X P n j false * E P n i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i) ∧
    (∀ i j, 1 ≤ i → i < n → 1 ≤ j → j ≤ n → i ≠ j → i+1 ≠ j →
      X P n i false * JM P n false j = JM P n false j * X P n i false ∧
      E P n i * JM P n false j = JM P n false j * E P n i) ∧
    (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      JM P n false i * JM P n false j = JM P n false j * JM P n false i) ∧
    (∀ i, 1 ≤ i → i < n →
      JM P n false i * X P n i false * JM P n false i * E P n i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i ∧
      E P n i * JM P n false i * X P n i false * JM P n false i = algebraMap R _ (↑P.lam⁻¹ : R) * E P n i) ∧
    (∀ i, 1 ≤ i → i < n → ∀ p : ℤ,
      E P n i * JPower P n (i+1) p = E P n i * JPower P n i (-p) ∧
      JPower P n (i+1) p * E P n i = JPower P n i (-p) * E P n i) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
