-- Prove2me | Theorems.Thm_SNumbers_sn_DiagCLMpq_le_of_exponent_ge
-- name    : SNumbers.sn_DiagCLMpq_le_of_exponent_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:25:36.338075+00:00
-- url     : https://prove2.me/theorems/611713fc-1ddf-5a46-9eb6-473ef28f1fa3
-- title:
--   SNumbers: sn Diag CLMpq le of exponent ge
-- statement:
--   **Universal upper bound for `q ≤ p`** (all s-numbers): `sₙ(D_σ) ≤ ‖σ_n‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L1038-L1042
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L1038-L1042

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

theorem SNumbers.sn_DiagCLMpq_le_of_exponent_ge {s : Family 𝕜} (hs : IsSNumberSequence s)
    (hqp : q ≤ p) (σ : Fin m → 𝕜) (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    s (DiagCLMpq p q σ) n ≤ ‖σ ⟨n, hn⟩‖ := by sorry
