-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_2_5
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.lemma_2_5
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:43:53.725999+00:00
-- url     : https://prove2.me/theorems/a0a00dc1-8087-47c9-918a-2fe56b0d9aff
-- title:
--   Lemma 2.5
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   Fix $1\le i<n$ and $p\in\mathbb Z$. For integers $s_1,\ldots,s_{i-1}$, put $U_s=(Y'_1)^{s_1}\cdots(Y'_{i-1})^{s_{i-1}}$. Then
--   $$
--   \begin{aligned}
--   e_i(Y'_i)^pe_i&\in\langle U_s e_i:s\in\mathbb Z^{i-1}\rangle,\\
--   X_i(Y'_i)^pe_i&\in\langle U_s(Y'_i)^t e_i:s\in\mathbb Z^{i-1},\ |t|\le|p|\rangle,\\
--   e_i(Y'_i)^pX_i&\in\langle e_iU_s(Y'_i)^t:s\in\mathbb Z^{i-1},\ |t|\le|p|\rangle.
--   \end{aligned}
--   $$
--   Only the final exponent $t$ is bounded. At $i=1$, $U_s=1$. These inclusions isolate the last winding exponent while allowing unrestricted earlier windings.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 8, Lemma 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Lemma 2.5, all (I)--(III), PDF pp.8--10. Only the LAST exponent is
bounded in (II) and (III); earlier exponents range independently over Z. -/
theorem lemma_2_5 (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    (E P n i * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ,
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * E P n i}) ∧
    (X P n i false * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t * E P n i}) ∧
    (E P n i * JPower P n i p * X P n i false ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = E P n i * ((List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t)}) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
