-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_3_15
-- name    : PostedPriceLimits.FullRevelation.lemma_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:43.103207+00:00
-- url     : https://prove2.me/theorems/774024a8-0203-41d4-b6c0-91c2f438214f
-- title:
--   Lemma 3.15 — comparison over consecutive geometric intervals
-- statement:
--   Let $s\in\mathbb Z_+$, $f,g:[\kappa]\to[0,1]$ and $a,b\ge0$. Suppose that for every $K\in\mathcal K_s$ and every pair of consecutive intervals $C,D\in\mathcal L(K)$ (with $D$ starting right after $C$ ends),
--   $$\mathrm{Avg}[f\mid C]\le a\,\mathrm{Avg}[g\mid D]+b.$$
--   Then
--   $$\sum_{k\in[\kappa]}f(k)\le2a\sum_{k\in[\kappa]}g(k)+b\kappa+5^s\sqrt\kappa.$$
--
--   In Lemma 5.14 this converts interval-wise affordability comparisons between owner ranks and non-owner ranks into a global comparison.
--
--   Differences from the source:
--   - reading: every pair of consecutive intervals C, D ∈ 𝓛(K) → ordered pairs with C immediately to the left of D; reason: the order is not stated; the proof uses exactly this order (|C| ≤ 2|D|), and requiring the hypothesis for fewer pairs gives the stronger statement
--   - encoding: f, g : [κ] → [0,1] → f, g : ℕ → ℝ with values in [0,1] on [κ]; reason: only the values on [κ] enter
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 3.15, p.7 (PDF 8); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Prelim

namespace PostedPriceLimits.FullRevelation

/-- Lemma 3.15. Let `s ∈ ℤ₊`, `f, g : [κ] → [0,1]` and `a, b ≥ 0`. If for every `K ∈ 𝒦_s`
and every pair of consecutive intervals `C, D ∈ L(K)` we have `Avg[f | C] ≤ a Avg[g | D] + b`,
then `∑_{k ∈ [κ]} f(k) ≤ 2a ∑_{k ∈ [κ]} g(k) + bκ + 5^s √κ`. -/
theorem lemma_3_15 (κ s : ℕ) (f g : ℕ → ℝ) (hf : ∀ k ∈ rankRange κ, f k ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ k ∈ rankRange κ, g k ∈ Set.Icc (0 : ℝ) 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ K ∈ rankPartition κ s, ∀ C ∈ geomPartition K, ∀ D ∈ geomPartition K,
      ConsecutiveIntervals C D → avg C f ≤ a * avg D g + b) :
    ∑ k ∈ rankRange κ, f k ≤ 2 * a * ∑ k ∈ rankRange κ, g k + b * κ + 5 ^ s * Real.sqrt κ := by sorry

end PostedPriceLimits.FullRevelation
