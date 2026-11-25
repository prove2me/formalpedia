-- Prove2me | Theorems.Thm_SNumbers_norm_idEmbed_le_one
-- name    : SNumbers.norm_idEmbed_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:03:00.933409+00:00
-- url     : https://prove2.me/theorems/2cb5141e-75a9-5a50-9dc0-2f7652408b33
-- title:
--   SNumbers: norm id Embed le one
-- statement:
--   **The identity embedding is a contraction** when `q ≤ p`: `‖id : ℓ^q_m → ℓ^p_m‖ ≤ 1`.
--   (The companion of `norm_idEmbed`, which computes the norm for `p ≤ q`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L976-L979
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L976-L979

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_DiagonalMatrices
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem SNumbers.norm_idEmbed_le_one [Nonempty (Fin m)] (hqp : q ≤ p) :
    ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ ≤ 1 := by sorry
