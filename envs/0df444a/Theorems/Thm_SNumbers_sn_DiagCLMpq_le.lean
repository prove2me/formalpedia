-- Prove2me | Theorems.Thm_SNumbers_sn_DiagCLMpq_le
-- name    : SNumbers.sn_DiagCLMpq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:25:20.227465+00:00
-- url     : https://prove2.me/theorems/c8b2539a-566e-4c1d-aa7a-1587cc680a54
-- title:
--   SNumbers: sn Diag CLMpq le
-- statement:
--   **Universal upper bound.** Every s-number sequence is bounded above by the
--   tail value: `sₙ(D_σ) ≤ (∑_{k≥n} ‖σ_k‖^r)^{1/r}` (`n ≤ m`). No ordering of the
--   diagonal or strictness is required.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L849-L853
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L849-L853

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

theorem SNumbers.sn_DiagCLMpq_le {s : Family 𝕜} (hs : IsSNumberSequence s) (hpq : p < q) (hq : q ≠ ∞)
    (σ : Fin m → 𝕜) {n : ℕ} (hn : n ≤ m) :
    s (DiagCLMpq p q σ) n ≤ diagTail p q σ n := by sorry
