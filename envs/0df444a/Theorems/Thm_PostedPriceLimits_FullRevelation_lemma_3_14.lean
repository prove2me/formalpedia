-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_3_14
-- name    : PostedPriceLimits.FullRevelation.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:34.422521+00:00
-- url     : https://prove2.me/theorems/b0ac6be5-d483-4bc1-a3e4-3cb9cf8b4545
-- title:
--   Lemma 3.14 — size of the iterated rank partition (corrected: empty partition at κ = 0)
-- statement:
--   For $\kappa\in\mathbb Z_+$ let $\mathcal K_s=\mathcal L^s(\{[\kappa]\})$ be the $s$-fold geometric refinement of the trivial partition of $[\kappa]=\{1,\dots,\kappa\}$, where $\mathcal L$ splits every interval into pieces of sizes $1,2,4,\dots$ from the right. Then for every $s\in\mathbb Z_+$,
--   $$|\mathcal K_s|\le5^s\sqrt\kappa.$$
--
--   The bound says the rank-information schedule $\mathcal K_0,\dots,\mathcal K_n$ stays coarse: after $s$ refinements the number of rank intervals is far below $\kappa$.
--
--   Differences from the source:
--   - correction: 𝒦₀ = {[κ]} even at κ = 0, since ℤ₊ includes zero → 𝒦₀ is the empty partition when κ = 0; the exact bound is unchanged; reason: at κ = s = 0 the literal source gives |{∅}| = 1 > 0 = 5⁰√0; discarding the empty part corrects this false corner and changes no positive-κ instance
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 3.14, p.7 (PDF 8); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Prelim

namespace PostedPriceLimits.FullRevelation

/-- Lemma 3.14 (corrected at `κ = 0`): `|𝒦_s| ≤ 5^s √κ`.
The literal source convention `𝒦₀ = {[κ]}` gives `1 ≤ 0` at `κ = s = 0`.
We use the empty partition of the empty rank set, retaining the exact bound at every
positive `κ` and making the zero-rank case valid. -/
theorem lemma_3_14 (κ s : ℕ) : ((rankPartition κ s).card : ℝ) ≤ 5 ^ s * Real.sqrt κ := by sorry

end PostedPriceLimits.FullRevelation
