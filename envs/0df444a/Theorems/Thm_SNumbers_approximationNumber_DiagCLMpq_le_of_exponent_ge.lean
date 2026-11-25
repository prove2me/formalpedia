-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_DiagCLMpq_le_of_exponent_ge
-- name    : SNumbers.approximationNumber_DiagCLMpq_le_of_exponent_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:12:58.338855+00:00
-- url     : https://prove2.me/theorems/b4765907-470c-4743-8155-199e597f7577
-- title:
--   SNumbers: approximation Number Diag CLMpq le of exponent ge
-- statement:
--   **Universal upper bound for `q ≤ p`** (approximation numbers): for a diagonal
--   non-increasing in modulus, `aₙ(D_σ) ≤ ‖σ_n‖` (`n < m`). Inherited from the
--   same-exponent value `aₙ(D_σ^{(q)}) = ‖σ_n‖` through the contraction `id`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L1016-L1035
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean#L1016-L1035

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

theorem SNumbers.approximationNumber_DiagCLMpq_le_of_exponent_ge (hqp : q ≤ p) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLMpq p q σ) n ≤ ‖σ ⟨n, hn⟩‖ := by sorry
