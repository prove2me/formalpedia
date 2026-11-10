-- Prove2me | Theorems.Thm_RevRedSAT_lemma_6_9
-- name    : RevRedSAT.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:47:41.825249+00:00
-- url     : https://prove2.me/theorems/80ff6679-c541-4243-b457-4b8ca6e0073e
-- title:
--   Lemma 6.9 — random bucket loads are at most $B_c$ with probability $1-q^{-5}$
-- statement:
--   Let $c\in\{1,2\}$ and $q\ge\max\{2,c\}$. Independently for each of $n$ elements, choose a uniformly random $c$-element subset of $[q]$, and put
--
--   $$B_c=1+\lceil 2cn/q\rceil+6\lceil\log_2q\rceil.$$
--
--   With probability at least $1-q^{-5}$, every bucket has at most $B_c$ candidates. For $c=1$, the same bound holds conditional on any fixed set $S$ of at most $q$ elements receiving distinct buckets.
--
--   **Formalization Note** The probability space is the finite set of maps from $[n]$ to the $c$-subsets of $[q]$ with the uniform measure; probabilities are ratios of counts.
--
--   Differences from the source:
--   - encoding: independent uniform random c-subsets, probability and conditional probability → ratios of counts over the uniform space of maps [n] → (c-subsets of [q]); reason: the product of uniform distributions is the uniform distribution on maps
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.9, p.43 (printed) = PDF p.45

import Mathlib
import Definitions.Def_RevRedSAT_Placeable

set_option autoImplicit false

namespace RevRedSAT

open Classical in
/-- **Lemma 6.9 (short candidate lists).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.9, p.43: "Let q ≥ max{2, c}, where c ∈ {1, 2}. Independently for each of n elements,
choose a uniformly random c-element subset of [q]. Put B_c = 1 + ⌈2cn/q⌉ + 6⌈log2 q⌉. With
probability at least 1 − q^{−5}, every bucket has at most B_c candidates. For c = 1, the same bound
holds conditional on any fixed set S of at most q elements receiving distinct buckets."

The sample space is the finite set of maps `g` from `[n]` to the `c`-element subsets of `[q]`, with
the uniform measure. The fraction of maps under which every bucket has at most `B_c` candidates is
at least `1 − q^{−5}`; for `c = 1` and every `S` with `|S| ≤ q`, the same holds for the fraction among
the maps giving the elements of `S` distinct buckets.

**Formalization Note** Probabilities are ratios of counts; `⌈log₂ q⌉` is `Nat.clog 2 q`. -/
theorem lemma_6_9 (n q c : ℕ) (hc : c = 1 ∨ c = 2) (hq : max 2 c ≤ q) :
    (1 - (q : ℝ) ^ (-5 : ℤ) ≤
      ((Finset.univ.filter fun g : Fin n → {T : Finset (Fin q) // T.card = c} =>
          ∀ b, bucketLoad (fun u => (g u).1) b ≤ 1 + ⌈(2 * c * n : ℝ) / q⌉₊ + 6 * Nat.clog 2 q).card : ℝ) /
        Fintype.card (Fin n → {T : Finset (Fin q) // T.card = c})) ∧
    (c = 1 → ∀ S : Finset (Fin n), S.card ≤ q →
      1 - (q : ℝ) ^ (-5 : ℤ) ≤
        ((Finset.univ.filter fun g : Fin n → {T : Finset (Fin q) // T.card = c} =>
            (∀ b, bucketLoad (fun u => (g u).1) b ≤ 1 + ⌈(2 * c * n : ℝ) / q⌉₊ + 6 * Nat.clog 2 q) ∧
            Set.InjOn (fun u => (g u).1) (S : Set (Fin n))).card : ℝ) /
          (Finset.univ.filter fun g : Fin n → {T : Finset (Fin q) // T.card = c} =>
            Set.InjOn (fun u => (g u).1) (S : Set (Fin n))).card) := by sorry

end RevRedSAT
