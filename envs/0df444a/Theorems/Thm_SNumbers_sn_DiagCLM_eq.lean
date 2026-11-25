-- Prove2me | Theorems.Thm_SNumbers_sn_DiagCLM_eq
-- name    : SNumbers.sn_DiagCLM_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:02:57.944591+00:00
-- url     : https://prove2.me/theorems/8d629b77-bad1-5b0c-8791-37df78d3858d
-- title:
--   SNumbers: sn Diag CLM eq
-- statement:
--   **Main result.** For every *strict* s-number sequence `s` and a diagonal
--   operator `D_σ : ℓ^p_m → ℓ^p_m` whose entries are non-increasing in modulus,
--   `sₙ(D_σ) = ‖σ_n‖` (the `(n+1)`-th largest entry), for `n < m`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L272-L278
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L272-L278

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

theorem SNumbers.sn_DiagCLM_eq {s : Family 𝕜} (hs : IsStrictSNumberSequence s)
    {σ : Fin m → 𝕜} (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    s (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ := by sorry
