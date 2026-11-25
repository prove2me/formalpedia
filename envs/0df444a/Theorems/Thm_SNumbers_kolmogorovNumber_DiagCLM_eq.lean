-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_DiagCLM_eq
-- name    : SNumbers.kolmogorovNumber_DiagCLM_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:24:50.895785+00:00
-- url     : https://prove2.me/theorems/f0b20fb3-f012-5820-873e-3701836a7c31
-- title:
--   SNumbers: kolmogorov Number Diag CLM eq
-- statement:
--   The Kolmogorov numbers of a diagonal operator: `dₙ(D_σ) = ‖σ_n‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L294-L297
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L294-L297

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

theorem SNumbers.kolmogorovNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    kolmogorovNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ := by sorry
