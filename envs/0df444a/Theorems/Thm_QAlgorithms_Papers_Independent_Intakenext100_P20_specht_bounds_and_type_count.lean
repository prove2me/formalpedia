-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_specht_bounds_and_type_count
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.specht_bounds_and_type_count
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:40:52.218345+00:00
-- url     : https://prove2.me/theorems/197202c7-666c-4526-a454-c23c501bd990
-- title:
--   Lemma 10, valid clauses (B1)–(B3)
-- statement:
--   Let $d,n\ge1$. Let $Y_n$ be the Young diagrams with $n$ boxes and at most $d$ rows, and write $\lambda=(\lambda_1\ge\cdots\ge\lambda_d\ge0)$ for padded row lengths. Put $b_i=\lambda_i/n$, $H(b)=-\sum_i b_i\log b_i$, and let $V_\lambda$ be the actual symmetric-group Specht factor. Then
--
--   $$e^{nH(b)}(n+d)^{-d(d+1)/2}\le\dim V_\lambda\le(n+d)^{2d}e^{nH(b)},\qquad |Y_n|\le(n+1)^d.$$
--
--   These are exactly clauses (B1)-(B3), which can be retained independently of the defective Schur-factor bound (B4).
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 9, Lemma 10, valid clauses (B1)–(B3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Lemma 10, PDF pp.9-10, precisely the valid clauses (B1)-(B3).
The separately false Schur-factor bound (B4) is excluded and deferred. -/
theorem specht_bounds_and_type_count {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (∀ shape : Schur.Partition d n,
      Real.exp ((n : ℝ) * shannonNats (Schur.normalizedRows hd hn shape)) * lowerPrefactor d n ≤
        (Module.finrank ℂ (Schur.spechtSpace shape) : ℝ) ∧
      (Module.finrank ℂ (Schur.spechtSpace shape) : ℝ) ≤
        (n + d : ℝ) ^ (2 * d) *
          Real.exp ((n : ℝ) * shannonNats (Schur.normalizedRows hd hn shape))) ∧
    Fintype.card (Schur.Partition d n) ≤ (n + 1) ^ d := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
