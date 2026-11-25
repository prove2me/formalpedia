-- Prove2me | Theorems.Thm_SNumbers_norm_idEmbed
-- name    : SNumbers.norm_idEmbed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:16:41.579854+00:00
-- url     : https://prove2.me/theorems/5ac4abcb-33f7-5ceb-a75b-9c40568c31d0
-- title:
--   SNumbers: norm id Embed
-- statement:
--   **Operator norm of the identity embedding** (`p ≤ q`):
--   `‖id : ℓ^q_m → ℓ^p_m‖ = m^{1/p - 1/q}`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L136-L149
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L136-L149

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

theorem SNumbers.norm_idEmbed [NeZero m] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) :
    ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ = (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by sorry
