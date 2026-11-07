-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_4
-- name    : RandOrderSort.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:14.243836+00:00
-- url     : https://prove2.me/theorems/d88c6ea0-6f53-4a5b-933e-cb1732f7a2ee
-- title:
--   Lemma 4.4 — reallocation requests between shrinking phases
-- statement:
--   Let $n\ge 8192$ and consider the reallocation at the start of shrinking phase $2\le i\le k$. Let $I$ be a current node interval containing $s$ buckets, formed by merging $2s$ buckets from phase $i-1$. Let $N_{i-1}(I)$ count arrivals canonical in $I$ during phase $i-1$, and let $N^{\mathrm{re}}_i(I)$ count the surviving empty cells whose reallocation requests are canonical in $I$. Then
--   $$N^{\mathrm{re}}_i(I)\le\max\{2(B+7)s-N_{i-1}(I),0\}.$$
--   If $i<k$ and these reallocation requests locally overflow $I$, then
--   $$N_{i-1}(I)<(B+14)s\le\frac{11}{10}Bs.$$
--
--   Excess empty-cell demand thus implies too few canonical arrivals in the preceding phase.
--
--   **Formalization Note** $\max\{\cdot,0\}$ is truncated subtraction in $\mathbb N$.
--
--   Differences from the source:
--   - encoding: I with s buckets in phase i, 2s buckets in phase i−1 → the node (h, idx) of the phase-i tree with s = 2^h, the node (h+1, idx) of the phase-(i−1) tree; reason: the same interval, by adjacent-pair merging
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.4, p.23, displays (24), (25)

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_Dop

namespace RandOrderSort

/-- **Lemma 4.4 (Reallocation requests between shrinking phases)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.23: "Consider the
reallocation at the start of shrinking phase 2 ≤ i ≤ k. Let I be a current node interval containing s
buckets, formed by merging 2s buckets from phase i − 1. Let N_{i−1}(I) count arrivals canonical in I
during phase i − 1, and let N^re_i(I) count the surviving empty cells whose reallocation requests are
canonical in I. Then N^re_i(I) ≤ max{2(B + 7)s − N_{i−1}(I), 0}. (24) If i < k and these
reallocation requests locally overflow I, then N_{i−1}(I) < (B + 14)s ≤ (11/10)Bs. (25)"

**Formalization Note.** For `n ≥ 8192` and every execution. Shrinking phase `i` is phase index
`L + i − 1`. `I` is the phase-`i` node `(h, idx)` with `s = 2^h` buckets; in the phase-`(i − 1)` tree
the same interval is the node `(h + 1, idx)`. `max{·, 0}` is truncated subtraction in `ℕ`. -/
theorem lemma_4_4 : ∀ n, 16 * T ≤ n → ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)),
    ∀ i, 2 ≤ i → i ≤ k n → ∀ h idx, 2 ^ h ≤ b n i → idx * 2 ^ h < b n i →
      Nop (opReqs (runOf x π σ) (L n + i - 1) false) h idx ≤
          2 * (B n + 7) * 2 ^ h - Nop (opReqs (runOf x π σ) (L n + i - 2) true) (h + 1) idx ∧
      (i < k n →
        capNode (b n i) (phaseCap n (L n + i - 1)) h idx <
            Nop (opReqs (runOf x π σ) (L n + i - 1) false) h idx →
          Nop (opReqs (runOf x π σ) (L n + i - 2) true) (h + 1) idx < (B n + 14) * 2 ^ h ∧
          (((B n + 14) * 2 ^ h : ℕ) : ℝ) ≤ 11 / 10 * (B n : ℝ) * 2 ^ h) := by sorry

end RandOrderSort
