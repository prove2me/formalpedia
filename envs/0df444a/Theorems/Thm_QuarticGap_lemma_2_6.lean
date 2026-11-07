-- Prove2me | Theorems.Thm_QuarticGap_lemma_2_6
-- name    : QuarticGap.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:21.21192+00:00
-- url     : https://prove2.me/theorems/578814e6-ba54-407c-ab76-ea8b705f255c
-- title:
--   Lemma 2.6 — $P(W \notin \mathcal G) \le 2\exp(-(8-2\log 9)n)$
-- statement:
--   If the entries of the $n \times n$ sign matrix $W$ are independent uniform signs, $n = 4^\ell$, then
--   $$
--   P(W \notin \mathcal G) \le \delta_n := 2\exp\bigl(-(8-2\log 9)n\bigr).
--   $$
--   Random signs thus satisfy the promise $\|W/\sqrt n\| \le 8$ except with exponentially small probability, so the promise costs the lower bound nothing.
--
--   Differences from the source:
--   - encoding: n a power of four, indices {0,1}^k → n = 4^ℓ, k = 2ℓ, √n = 2^ℓ; reason: the same values of n
--   - encoding: independent uniform signs, uniformly random f or W → the uniform distribution on the finite set of sign functions; reason: the same law
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 2.6, p.18

import Mathlib
import Definitions.Def_QuarticGap_Ahat

open QAlgorithms

namespace QuarticGap

/-- Lemma 2.6 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.18). If the entries of `W` are independent
uniform signs, then `P(W ∉ G) ≤ δ_n := 2 exp(−(8 − 2 log 9)n)`, with `n = 4^ℓ`. -/
theorem lemma_2_6 (ℓ : ℕ) :
    uProb (fun W : SignMat ℓ => W ∉ G ℓ) ≤
      2 * Real.exp (-(8 - 2 * Real.log 9) * 4 ^ ℓ) := by sorry

end QuarticGap
