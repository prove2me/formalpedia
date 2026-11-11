-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_corollary_3_26
-- name    : RandProdExp.TwoSided.corollary_3_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:17:51.390198+00:00
-- url     : https://prove2.me/theorems/02d14559-e0b4-4951-b6ae-c2a21ecfa15c
-- title:
--   Corollary 3.26 — a prime not dividing $m$ in $(q,\,C(q+\log 2m)]$
-- statement:
--   There is a universal constant $C$ such that for every real $q\ge2$ and every integer $m\ge1$ there is a prime $p$ with $p\nmid m$ and
--   $$q<p\le C\big(q+\log(2m)\big),$$
--   $\log$ the natural logarithm. It is used to choose one characteristic that avoids every integer certificate of the transfer from $\mathbb R$ to finite fields.
--
--   Differences from the source:
--   - reading: every m ∈ ℕ → every m : ℕ with 1 ≤ m; reason: for m = 0 every prime divides m and log(2m) is undefined; the proof sets ℓ = log(2m) and the only use (Theorem 6.1, Step 3) has m* ≥ 1
--   - reading: q ≥ 2 (domain not stated) → q : ℝ with 2 ≤ q; reason: the corollary is applied with the real q = 2 + L log(n + 1) (p. 44) and q = max{2D + 1, d log(n + 1)} (p. 42)
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 25, Corollary 3.26

import Mathlib

namespace RandProdExp.TwoSided

/-- **Corollary 3.26** (p. 25). There is a universal constant `C` such that for all `q ≥ 2` and every
`m ∈ ℕ` (read as `m ≥ 1`) there is a prime `p ∤ m` with `q < p ≤ C (q + log(2m))` (natural log). -/
theorem corollary_3_26 :
    ∃ C : ℝ, ∀ q : ℝ, 2 ≤ q → ∀ m : ℕ, 1 ≤ m →
      ∃ p : ℕ, p.Prime ∧ ¬ p ∣ m ∧ q < (p : ℝ) ∧ (p : ℝ) ≤ C * (q + Real.log (2 * (m : ℝ))) := by sorry

end RandProdExp.TwoSided
