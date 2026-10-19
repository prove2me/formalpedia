-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_finiteExpurgatedBound
-- name    : QAlgorithms.Papers.Independent.Information100.P58.finiteExpurgatedBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:21:53.243822+00:00
-- url     : https://prove2.me/theorems/b915e162-d6f4-40fa-9ce8-e9c11363b5dc
-- title:
--   Finite expurgated maximum-error bound
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For every integer $M\ge1$ and every fixed real $s\ge1$, set $a_s=d^{-1}+(1-d^{-1})p^{1/s}$. There exists a deterministic classical no-feedback word code whose uniform-compatible-message decoder has maximum error at most
--
--   $$\frac12\left[2(2M-1)a_s^n\right]^s.$$
--
--   The code may depend on $s$ and needs no shared randomness. The right side may exceed one; it is an error upper bound rather than a probability identity.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 46, Appendix B, Eq. (B.4)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Appendix B, Eq.(B.4), PDF p.46: finite deterministic maximum-error expurgation, for each fixed real s≥1. -/
theorem finiteExpurgatedBound (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p s : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (hs : 1 ≤ s) :
    ∃ C : Fin M → Word n d, ∀ m,
      1-deterministicIndividual p C m ≤ expurgatedBound n d M p s := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
