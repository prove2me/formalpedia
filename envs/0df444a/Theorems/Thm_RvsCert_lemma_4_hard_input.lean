-- Prove2me | Theorems.Thm_RvsCert_lemma_4_hard_input
-- name    : RvsCert.lemma_4_hard_input
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:48:15.63326+00:00
-- url     : https://prove2.me/theorems/7dbf119f-bc2c-4e17-9d6a-47d3c09882de
-- title:
--   Proof of Lemma 4 — the all-$\bot$ input has no certificate of $n^2/2$ bits
-- statement:
--   Let $n>0$ and let $x_0$ be the input whose race lists are filled with $\bot$ and whose proposal cards are filled with $0$ (in the binary encoding, the all-zero bit string). Then $f_n(x_0)=0$, and every certificate $S$ for $x_0$ reveals more than $n^2/2$ bits:
--   $$
--   |S|>\frac{n^2}{2}.
--   $$
--
--   Differences from the source:
--   - encoding: the function f on (X, Y) with numbers in log n bits → the bit layout `Idx n` with fixed widths wX n = ⌈log₂(2n²+1)⌉, wY n = ⌊log₂ n⌋+1, ⊥ = 0, athlete (c,b) = 1+cn+b, 0-based positions, card entry j for the j-th opponent in increasing order; reason: the paper fixes only O(log n)-bit numbers; this is one such injective encoding
--   - reading: any certificate that exhibits n²/2 bits of this input cannot certify that f(X,Y) = 0 → every certificate S of x₀ has |S| > n²/2; reason: a certificate of at most n²/2 bits is excluded; a subset of a non-certificate is a non-certificate, so 'exactly' and 'at most' n²/2 bits say the same
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, proof of Lemma 4, p.3

import Mathlib
import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_IsCertificate

namespace RvsCert

/-- **Proof of Lemma 4, the hard 0-input** (p.3 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "Consider the input
(X, Y) where the X lists for each race are filled with ⊥ and the Y lists for each athlete are
filled with 0. This is clearly an input with f(X, Y) = 0. … Any certificate that exhibits n²/2
bits of this input cannot certify that f(X, Y) = 0." In the binary encoding this is the all-false
input; `champion n` is `false` on it, and every certificate for it has more than `n²/2` bits. -/
theorem lemma_4_hard_input (n : ℕ) (hn : 0 < n) :
    champion n (fun _ => false) = false ∧
    ∀ S : Finset (Idx n), IsCertificate (champion n) (fun _ => false) S →
      (n : ℝ) ^ 2 / 2 < S.card := by sorry

end RvsCert
