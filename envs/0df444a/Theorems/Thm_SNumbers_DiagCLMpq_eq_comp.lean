-- Prove2me | Theorems.Thm_SNumbers_DiagCLMpq_eq_comp
-- name    : SNumbers.DiagCLMpq_eq_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:03:57.882375+00:00
-- url     : https://prove2.me/theorems/da7649d6-ee91-4adb-ae11-3b891f84c983
-- title:
--   SNumbers: Diag CLMpq eq comp
-- statement:
--   **Factorisation through the same-exponent diagonal**:
--   `D_σ : ℓ^q_m → ℓ^p_m` equals the identity embedding `ℓ^q_m → ℓ^p_m` after the
--   same-exponent diagonal `D_σ : ℓ^q_m → ℓ^q_m`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L984-L986
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L984-L986

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

theorem SNumbers.DiagCLMpq_eq_comp (σ : Fin m → 𝕜) :
    DiagCLMpq p q σ = (idEmbed p q).comp (DiagCLM q σ) := by sorry
