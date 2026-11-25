-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_DiagCLM_eq
-- name    : SNumbers.bernsteinNumber_DiagCLM_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:25:30.935902+00:00
-- url     : https://prove2.me/theorems/41824aad-cca6-478b-8a3f-dcd350f3b667
-- title:
--   SNumbers: bernstein Number Diag CLM eq
-- statement:
--   The Bernstein numbers of a diagonal operator: `bₙ(D_σ) = ‖σ_n‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L300-L303
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L300-L303

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

theorem SNumbers.bernsteinNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    bernsteinNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ := by sorry
