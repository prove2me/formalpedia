-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_proposition_2_3
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.proposition_2_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:42:34.172191+00:00
-- url     : https://prove2.me/theorems/6306c8b9-e30c-457e-9916-213b2769aca2
-- title:
--   Proposition 2.3
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   For every valid index $i$,
--   $$
--   e_ie_{i+1}e_{i+2}\gamma_i=\gamma_{i+2}e_ie_{i+1}e_{i+2}\quad(\gamma=X,e,Y'),
--   $$
--   $$
--   X_iX_{i+1}\gamma_i=\gamma_{i+1}X_iX_{i+1}\quad(\gamma=X,e).
--   $$
--   These identities move generators through short chains. The paper explicitly restates the calculation attributed to Yu's thesis [37], Proposition 1.3.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 6, Proposition 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Proposition 2.3, both (23) and (24) and every choice of gamma, PDF p.6.
The cited calculation is Proposition 1.3 of Yu's thesis [37]. -/
theorem proposition_2_3 :
    (∀ i, 1 ≤ i → i+2 < n → ∀ g : ℕ → NonsplitBMW P n,
      (g = (fun j => X P n j false) ∨ g = E P n ∨ g = JM P n false) →
      E P n i * E P n (i+1) * E P n (i+2) * g i =
        g (i+2) * E P n i * E P n (i+1) * E P n (i+2)) ∧
    (∀ i, 1 ≤ i → i+1 < n → ∀ g : ℕ → NonsplitBMW P n,
      (g = (fun j => X P n j false) ∨ g = E P n) →
      X P n i false * X P n (i+1) false * g i =
        g (i+1) * X P n i false * X P n (i+1) false) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
