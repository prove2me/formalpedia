-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_thresholdedMaximumError
-- name    : QAlgorithms.Papers.Independent.Information100.P58.thresholdedMaximumError
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:19:32.227987+00:00
-- url     : https://prove2.me/theorems/da8a257f-da16-4467-9064-276ae9c90e56
-- title:
--   Thresholded maximum-error bound
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For every integer $M\ge1$ and every real threshold $r$, a deterministic classical no-feedback word code exists whose uniform-compatible-message decoder has individual-message errors bounded by
--
--   $$\min\left\{1,\sum_{0\le k\le n:k<r}b_k+(2M-1)\sum_{0\le k\le n:k\ge r}b_kd^{-k}\right\}.$$
--
--   Thus the same expression bounds maximum error without shared randomness. The low-survivor tail has coefficient one, including when $r$ lies outside $[0,n]$.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 34, Lemma 8.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Lemma 8.3, PDF pp.34–35: thresholded deterministic maximum-error bound, for every real threshold. -/
theorem thresholdedMaximumError (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p r : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    ∃ C : Fin M → Word n d, ∀ m,
      1-deterministicIndividual p C m ≤ thresholdBound n d M p r := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
