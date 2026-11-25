-- Prove2me | Theorems.Thm_SNumbers_norm_DiagCLMpq_iSup
-- name    : SNumbers.norm_DiagCLMpq_iSup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:25:33.867172+00:00
-- url     : https://prove2.me/theorems/4c92d739-40a1-51a7-849c-c285cbc8243e
-- title:
--   SNumbers: norm Diag CLMpq i Sup
-- statement:
--   **Operator norm for `q ≤ p`**: `‖D_σ : ℓ^q_m → ℓ^p_m‖ = ⨆ i, ‖σ i‖`, the
--   largest diagonal modulus (`= ‖σ‖_{ℓ^∞}`; `⨆` is the supremum).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L990-L1011
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L990-L1011

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

theorem SNumbers.norm_DiagCLMpq_iSup [Nonempty (Fin m)] (hqp : q ≤ p) (σ : Fin m → 𝕜) :
    ‖DiagCLMpq p q σ‖ = ⨆ i, ‖σ i‖ := by sorry
