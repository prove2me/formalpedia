-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_idEmbed_le
-- name    : SNumbers.approximationNumber_idEmbed_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:59:06.457568+00:00
-- url     : https://prove2.me/theorems/a1d6d1f5-9b8a-4111-8919-e4af659bbf22
-- title:
--   SNumbers: approximation Number id Embed le
-- statement:
--   **Upper bound.** The `n`-th approximation number of `id : ℓ^q_m → ℓ^p_m`
--   (`p ≤ q`) is at most `(m-n)^{1/p-1/q}`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L178-L217
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L178-L217

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}

theorem SNumbers.approximationNumber_idEmbed_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n ≤ m) :
    approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n
      ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by sorry
