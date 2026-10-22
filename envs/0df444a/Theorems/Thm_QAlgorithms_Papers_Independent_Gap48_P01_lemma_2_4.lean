-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_2_4
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.lemma_2_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:43:10.892527+00:00
-- url     : https://prove2.me/theorems/82dfaa8d-ca38-45a3-893e-b47c311d5cb4
-- title:
--   Lemma 2.4
-- statement:
--   Let $k\ge1$ and $n\ge0$, and let $R$ be a commutative unital ring with units $q_0,q,\lambda$ and arbitrary scalars $q_1,\ldots,q_{k-1},A_0,\ldots,A_{k-1}$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B_n^k(R)$ be the algebra of Definition 2.1, with its full relations (1)–(15). Write $X_i,e_i,Y$ for its generators and $Y'_i=X_{i-1}\cdots X_1YX_1\cdots X_{i-1}$ for $1\le i\le n$. All indices below are restricted so the displayed generators exist.
--
--   Fix $1\le i<n$ and a nonnegative integer $p$, and abbreviate $x=X_i$, $e=e_i$, $u=Y'_i$, $v=Y'_{i+1}$. Then
--   $$
--   \begin{aligned}
--   xu^p&=v^px-\delta\sum_{s=1}^p v^su^{p-s}+\delta\sum_{s=1}^p v^seu^{p-s},\\
--   xu^{-p}&=v^{-p}x+\delta\sum_{s=1}^p v^{s-p}u^{-s}-\delta\sum_{s=1}^p v^{s-p}eu^{-s},\\
--   xv^p&=u^px+\delta\sum_{s=1}^p u^{p-s}v^s-\delta\sum_{s=1}^p u^{p-s}ev^s,\\
--   xv^{-p}&=u^{-p}x-\delta\sum_{s=1}^p u^{-s}v^{s-p}+\delta\sum_{s=1}^p u^{-s}ev^{s-p},\\
--   xu^px&=v^p-\delta\sum_{s=1}^{p-1}v^su^{p-s}x+\delta\sum_{s=1}^{p-1}v^seu^{p-s}x\quad(p\ge1),\\
--   xu^px&=v^p-\delta\sum_{s=1}^{p-1}xu^sv^{p-s}+\delta\sum_{s=1}^{p-1}xu^sev^{p-s}\quad(p\ge1),\\
--   xu^{-p}x&=v^{-p}+\delta\sum_{s=0}^p v^{s-p}u^{-s}x-\delta\sum_{s=0}^p v^{s-p}eu^{-s}x,\\
--   xu^{-p}x&=v^{-p}+\delta\sum_{s=0}^p xu^{-s}v^{s-p}-\delta\sum_{s=0}^p xu^{-s}ev^{s-p}.
--   \end{aligned}
--   $$
--   These formulas control powers in alpha chains. Empty sums are zero. Source correction: only the fifth and sixth lines require $p\ge1$; their printed $p=0$ cases would incorrectly assert $X_i^2=1$. The source's derivation from (25) and (17) supports the correction, which was independently accepted in rounds 1 and 2.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 7, Lemma 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- Lemma 2.4, all eight identities (25)--(32), PDF p.7.
SOURCE CORRECTION: the printed blanket p>=0 is changed to p>=1 for (29)
and (30) only. At p=0 those two would assert X_i^2=1, contradicting (17).
The source derivation from (25) and (17) uses p>=1.
Equation (28) retains the source's plus before its final sum.
Round 2 independently accepts the exponent-domain correction above. -/
theorem lemma_2_4 (i p : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    (X P n i false * JPower P n i p = JPower P n (i+1) p * X P n i false -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) s * JPower P n i ((p:ℤ)-s)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) s * E P n i * JPower P n i ((p:ℤ)-s))) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) = JPower P n (i+1) (-(p:ℤ)) * X P n i false +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) ((s:ℤ)-p) * JPower P n i (-(s:ℤ))) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) ((s:ℤ)-p) * E P n i * JPower P n i (-(s:ℤ)))) ∧
    (X P n i false * JPower P n (i+1) p = JPower P n i p * X P n i false +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i ((p:ℤ)-s) * JPower P n (i+1) s) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i ((p:ℤ)-s) * E P n i * JPower P n (i+1) s)) ∧
    (X P n i false * JPower P n (i+1) (-(p:ℤ)) = JPower P n i (-(p:ℤ)) * X P n i false -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i (-(s:ℤ)) * JPower P n (i+1) ((s:ℤ)-p)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i (-(s:ℤ)) * E P n i * JPower P n (i+1) ((s:ℤ)-p))) ∧
    (1 ≤ p → X P n i false * JPower P n i p * X P n i false = JPower P n (i+1) p -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), JPower P n (i+1) s * JPower P n i ((p:ℤ)-s) * X P n i false) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), JPower P n (i+1) s * E P n i * JPower P n i ((p:ℤ)-s) * X P n i false)) ∧
    (1 ≤ p → X P n i false * JPower P n i p * X P n i false = JPower P n (i+1) p -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), X P n i false * JPower P n i s * JPower P n (i+1) ((p:ℤ)-s)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), X P n i false * JPower P n i s * E P n i * JPower P n (i+1) ((p:ℤ)-s))) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) * X P n i false = JPower P n (i+1) (-(p:ℤ)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, JPower P n (i+1) ((s:ℤ)-p) * JPower P n i (-(s:ℤ)) * X P n i false) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, JPower P n (i+1) ((s:ℤ)-p) * E P n i * JPower P n i (-(s:ℤ)) * X P n i false)) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) * X P n i false = JPower P n (i+1) (-(p:ℤ)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, X P n i false * JPower P n i (-(s:ℤ)) * JPower P n (i+1) ((s:ℤ)-p)) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, X P n i false * JPower P n i (-(s:ℤ)) * E P n i * JPower P n (i+1) ((s:ℤ)-p))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Gap48.P01

end
