-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_theorem_1_1_steps_first
-- name    : PolyEvalDS.LargeChar.theorem_1_1_steps_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:29.549401+00:00
-- url     : https://prove2.me/theorems/981bbec6-03fe-4875-8880-4fb0f930a59e
-- title:
--   Proof of Theorem 1.1, first recursion bound (p. 8) — $\lceil\tilde k\rceil$ steps reach $\ln B_i\le d$
-- statement:
--   Let $(B_i)$ be the curve recursion with $B_0=p$, and let
--   $$\tilde k=\log_2\ln\ln p+1-\log_2\ln d.$$
--   There is $d_0$ such that for all $d\ge d_0$ and all naturals $p>d^{60}$ there is an index $k\le\lceil\tilde k\rceil$ with
--   $$\ln B_k\le d.$$
--
--   This bounds the first phase of the recursion behind Theorem 1.1, in which each step shrinks $\ln B_i$ by roughly a square root.
--
--   **Formalization Note** $\lceil\tilde k\rceil$ is the ceiling truncated at $0$. That covers $\tilde k<0$, where $k=0$ works.
--
--   Differences from the source:
--   - generalization: p is a prime → p is any natural number with p > d⁶⁰; reason: the sequence uses p only as a real number; primes are a special case
--   - encoding: "assume wlog p > d⁶⁰" in the proof → p > d⁶⁰ is a hypothesis of this item; reason: this item formalizes that branch of the proof; the goal and Theorem 1.1 cover all primes p > 2
--   - reading: "for sufficiently large d" → one d₀ before d and p; reason: the threshold of the proof is absolute
--   - encoding: let k be the smallest integer with ln B_k ≤ d, so we have to show k ≤ ⌈k̃⌉; assume k̃ ≥ 0 → there is k ≤ ⌈k̃⌉₊ with ln B_k ≤ d, the ceiling truncated at 0; reason: some index below the bound holds exactly when the smallest one does; k̃ < 0 forces ln p < d and k = 0
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, proof of Theorem 1.1, p. 8

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Recursions

namespace PolyEvalDS.LargeChar

/-- Proof of Theorem 1.1, p. 8: `⌈k̃⌉` steps reach `ln B_i ≤ d`, with
`k̃ = log₂ ln ln p + 1 − log₂ ln d`. -/
theorem theorem_1_1_steps_first :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → d ^ 60 < p →
      ∃ k : ℕ,
        k ≤ ⌈Real.logb 2 (Real.log (Real.log p)) + 1 - Real.logb 2 (Real.log d)⌉₊ ∧
          Real.log (curveSeq p d k) ≤ (d : ℝ) := by sorry

end PolyEvalDS.LargeChar
