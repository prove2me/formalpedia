-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_theorem_1_1_point_count
-- name    : PolyEvalDS.LargeChar.theorem_1_1_point_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:31.751708+00:00
-- url     : https://prove2.me/theorems/5e1ac228-561e-4ada-b38f-7574dabe092f
-- title:
--   Proof of Theorem 1.1, total number of points (p. 9) — the product of the query counts is at most $(18d)^{k+l}d\ln p$
-- statement:
--   Let $(B_i)$ be the curve recursion with $B_0=p$. There is $d_0$ such that for all $d\ge d_0$ and naturals $p>d^{60}$: if $k$ is the least index with $\ln B_k\le d$ and $l$ is the least index with $B_{k+l}\le d^{60}$, then
--   $$\prod_{i=0}^{k-1}\Bigl(d\Bigl\lceil\sqrt{\frac{\ln B_i}{\ln\ln B_i}}\Bigr\rceil+1\Bigr)\ \prod_{i=0}^{l-1}\Bigl(d\Bigl\lceil\sqrt{\frac{\ln B_{k+i}}{\ln d}}\Bigr\rceil+1\Bigr)\le(18d)^{k+l}\,d\ln p.$$
--
--   Each factor is the query count $rd+1$ of one application of Proposition 3.2, so the left side counts the cells read by the composed recursion. Together with the two recursion bounds this gives the query complexity of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: p is a prime → p is any natural number with p > d⁶⁰; reason: the sequence uses p only as a real number; primes are a special case
--   - encoding: "assume wlog p > d⁶⁰" in the proof → p > d⁶⁰ is a hypothesis of this item; reason: this item formalizes that branch of the proof; the goal and Theorem 1.1 cover all primes p > 2
--   - reading: "for sufficiently large d" → one d₀ before d and p; reason: the threshold of the proof is absolute
--   - encoding: ≤ (18d)^{k+l} d ln p = (18d)^{k+l+O(1)} ln p, after a displayed chain of intermediate inequalities → only the end-to-end bound (18d)^{k+l} d ln p; reason: the right-hand form is the same bound with the factor d written as a power of 18d, and the middle lines are steps of its proof
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, proof of Theorem 1.1, p. 9

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Recursions

namespace PolyEvalDS.LargeChar

/-- Proof of Theorem 1.1, p. 9: with `k` the least index with `ln B_k ≤ d` and `l` the least index
with `B_{k+l} ≤ d⁶⁰`, the product of the per-step query counts is at most `(18d)^{k+l} d ln p`. -/
theorem theorem_1_1_point_count :
    ∃ d₀ : ℕ, ∀ d p k l : ℕ, d₀ ≤ d → d ^ 60 < p →
      (∀ i < k, (d : ℝ) < Real.log (curveSeq p d i)) →
      Real.log (curveSeq p d k) ≤ (d : ℝ) →
      (∀ i < l, (d : ℝ) ^ 60 < curveSeq p d (k + i)) →
      curveSeq p d (k + l) ≤ (d : ℝ) ^ 60 →
      (∏ i ∈ Finset.range k,
          ((d : ℝ) * (⌈Real.sqrt (Real.log (curveSeq p d i) /
            Real.log (Real.log (curveSeq p d i)))⌉₊ : ℝ) + 1)) *
        (∏ i ∈ Finset.range l,
          ((d : ℝ) * (⌈Real.sqrt (Real.log (curveSeq p d (k + i)) / Real.log d)⌉₊ : ℝ) + 1)) ≤
        (18 * (d : ℝ)) ^ (k + l) * (d : ℝ) * Real.log p := by sorry

end PolyEvalDS.LargeChar
