-- Prove2me | Theorems.Thm_PhaseRetrieval_integral_norm_sq_fourier_sum
-- name    : PhaseRetrieval.integral_norm_sq_fourier_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:07.400638+00:00
-- url     : https://prove2.me/theorems/615ea02e-1812-4bdf-980e-e7e1811cb103
-- title:
--   Phase Retrieval: integral norm sq fourier sum
-- statement:
--   Parseval's identity for a finite Fourier sum with injectively indexed frequencies.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/FourierParseval.lean#L18-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/FourierParseval.lean#L18-L55

module
public import Mathlib.Analysis.Fourier.AddCircle
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
set_option autoImplicit true
@[expose] public section
open MeasureTheory Complex
open scoped BigOperators
open PhaseRetrieval

theorem PhaseRetrieval.integral_norm_sq_fourier_sum {ι : Type*} [Fintype ι]
    {period : ℝ} [Fact (0 < period)] (frequencies : ι ↪ ℤ) (coefficients : ι → ℂ) :
    (∫ t : AddCircle period,
      ‖∑ i : ι, coefficients i * fourier (frequencies i) t‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ i : ι, ‖coefficients i‖ ^ 2 := by sorry
