-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_classicalRandomCodingBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P58.classicalRandomCodingBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:18:46.992147+00:00
-- url     : https://prove2.me/theorems/6a592b07-845a-4922-8293-39e2a16fed11
-- title:
--   Classical random-coding success and error bounds
-- statement:
--   Let $n\ge1$ be the blocklength, $d\ge2$ the input dimension, and $p\in[0,1]$ the erasure probability. Each use of $\mathcal E_p$ transmits the input unchanged with probability $1-p$ and otherwise returns a one-dimensional orthogonal erasure flag. Write $w_S=(1-p)^{|S|}p^{n-|S|}$, $D_S=d^{|S|}$, and $b_k=\binom nk(1-p)^kp^{n-k}$. For $M\ge1$ equiprobable messages, write $s_{n,d,p}(M)=\sum_{k=0}^n b_k\min\{1,d^k/M\}$. Let $P_{\rm cl}^*$ and $P_{\rm q}^*$ denote the optimal average no-feedback success for classical and unrestricted quantum encodings, respectively. Define
--
--   $$a_{n,d,p}(M)=\sum_{k=0}^n b_k\frac{d^k}{M}[1-(1-d^{-k})^M].$$
--
--   Then
--
--   $$(1-e^{-1})s_{n,d,p}(M)\le a_{n,d,p}(M)\le P_{\rm cl}^*\le P_{\rm q}^*\le s_{n,d,p}(M).$$
--
--   There exists a deterministic classical code with average success at least $a_{n,d,p}(M)$, and there also exists a deterministic classical code with average error at most
--
--   $$U_n(M)=\sum_{k=0}^n b_k\min\{1,(M-1)/(2d^k)\}.$$
--
--   Both use uniform guessing among compatible messages. The two codebooks may differ, and neither needs shared randomness.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 33, Proposition 8.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Proposition 8.2, PDF pp.33–34: full success chain and two possibly different deterministic code witnesses. -/
theorem classicalRandomCodingBounds (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (1-Real.exp (-1))*dimensionSuccess n d p M ≤ randomCodingSuccess n d M p ∧
    randomCodingSuccess n d M p ≤ classicalOptimum n d M p ∧
    classicalOptimum n d M p ≤ quantumOptimum n d M p ∧
    quantumOptimum n d M p ≤ dimensionSuccess n d p M ∧
    (∃ C : Fin M → Word n d, randomCodingSuccess n d M p ≤ deterministicAverage p C) ∧
    (∃ C : Fin M → Word n d, 1-deterministicAverage p C ≤ collisionBound n d M p) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
