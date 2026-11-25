-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_DiagCLM_le
-- name    : SNumbers.hilbertNumber_DiagCLM_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:25:05.991596+00:00
-- url     : https://prove2.me/theorems/bf67d6d8-d763-5d1e-83e3-41cbeb573853
-- title:
--   SNumbers: hilbert Number Diag CLM le
-- statement:
--   The Hilbert numbers of a diagonal operator satisfy `hₙ(D_σ) ≤ ‖σ_n‖`. Unlike
--   the strict s-numbers above, equality can fail for `p ≠ 2`: the Hilbert numbers
--   measure the Hilbertian part of `ℓ^p`, which is genuinely smaller.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L308-L312
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L308-L312

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

theorem SNumbers.hilbertNumber_DiagCLM_le {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    hilbertNumber (DiagCLM p σ) n ≤ ‖σ ⟨n, hn⟩‖ := by sorry
