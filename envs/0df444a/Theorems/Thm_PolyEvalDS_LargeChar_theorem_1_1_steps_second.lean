-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_theorem_1_1_steps_second
-- name    : PolyEvalDS.LargeChar.theorem_1_1_steps_second
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:26.998621+00:00
-- url     : https://prove2.me/theorems/cd87dff0-c26a-4d87-b0c7-37de7963cf8c
-- title:
--   Proof of Theorem 1.1, second recursion bound (p. 9) — $\lceil\tilde l\rceil$ further steps reach $d^{60}$
-- statement:
--   Let $(B_i)$ be the curve recursion with $B_0=p$. There is $d_0$ such that for all $d\ge d_0$, all naturals $p>d^{60}$ and every $k$ that is the least index with $\ln B_k\le d$, there is
--   $$l\le\lceil\tilde l\rceil,\qquad \tilde l=\log_2\ln\Bigl(\frac{\ln B_k}{\ln d}\Bigr),$$
--   with
--   $$B_{k+l}\le d^{60}.$$
--
--   This bounds the second phase of the recursion, after which the box $\{0,\dots,d^{60}\}^n$ of Theorem 1.1 is reached.
--
--   **Formalization Note** $\lceil\tilde l\rceil$ is the ceiling truncated at $0$; when $\ln B_k\le e\ln d$ then $l=0$ works, so a nonpositive value of $\tilde l$ does no harm.
--
--   Differences from the source:
--   - generalization: p is a prime → p is any natural number with p > d⁶⁰; reason: the sequence uses p only as a real number; primes are a special case
--   - encoding: "assume wlog p > d⁶⁰" in the proof → p > d⁶⁰ is a hypothesis of this item; reason: this item formalizes that branch of the proof; the goal and Theorem 1.1 cover all primes p > 2
--   - reading: "for sufficiently large d" → one d₀ before d and p; reason: the threshold of the proof is absolute
--   - encoding: let l be the smallest integer such that B_{k+l} ≤ d⁶⁰, so we have to show l ≤ ⌈l̃⌉ → there is l ≤ ⌈l̃⌉₊ with B_{k+l} ≤ d⁶⁰, the ceiling truncated at 0, with k stated as least by two hypotheses; reason: some index below the bound holds exactly when the smallest one does; the page takes l̃ = log₂ ln(ln B_k/ln d) and the value is nonpositive only where l = 0
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, proof of Theorem 1.1, p. 9

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Recursions

namespace PolyEvalDS.LargeChar

/-- Proof of Theorem 1.1, p. 9: for `k` the least index with `ln B_k ≤ d`, `⌈l̃⌉` further steps
reach `d⁶⁰`, with `l̃ = log₂ ln(ln B_k / ln d)`. -/
theorem theorem_1_1_steps_second :
    ∃ d₀ : ℕ, ∀ d p k : ℕ, d₀ ≤ d → d ^ 60 < p →
      (∀ i < k, (d : ℝ) < Real.log (curveSeq p d i)) →
      Real.log (curveSeq p d k) ≤ (d : ℝ) →
      ∃ l : ℕ,
        l ≤ ⌈Real.logb 2 (Real.log (Real.log (curveSeq p d k) / Real.log d))⌉₊ ∧
          curveSeq p d (k + l) ≤ (d : ℝ) ^ 60 := by sorry

end PolyEvalDS.LargeChar
