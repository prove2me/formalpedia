-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_idEmbed_eq
-- name    : SNumbers.approximationNumber_idEmbed_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:58:52.993532+00:00
-- url     : https://prove2.me/theorems/433b1798-8a33-52fc-8ee5-70958bac75ed
-- title:
--   SNumbers: approximation Number id Embed eq
-- statement:
--   **The approximation numbers of the identity embedding** (`p ≤ q`):
--   `aₙ(id : ℓ^q_m → ℓ^p_m) = (m-n)^{1/p-1/q}`, via the geometric input
--   `exists_norm_ratio_ge_idEmbed`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L340-L344
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L340-L344

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

theorem SNumbers.approximationNumber_idEmbed_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n
      = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by sorry
