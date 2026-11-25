-- Prove2me | Theorems.Thm_SNumbers_le_approximationNumber_idEmbed
-- name    : SNumbers.le_approximationNumber_idEmbed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:59:02.685632+00:00
-- url     : https://prove2.me/theorems/164d3b2d-95ad-4d78-a7c1-8664a7efa449
-- title:
--   SNumbers: le approximation Number id Embed
-- statement:
--   **Lower bound.** `(m-n)^{1/p-1/q} ≤ aₙ(id : ℓ^q_m → ℓ^p_m)` (`p ≤ q`),
--   via the geometric input `exists_norm_ratio_ge_idEmbed`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L310-L335
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L310-L335

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

theorem SNumbers.le_approximationNumber_idEmbed {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal)
      ≤ approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n := by sorry
