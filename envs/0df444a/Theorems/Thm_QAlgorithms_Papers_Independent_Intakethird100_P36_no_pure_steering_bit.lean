-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_no_pure_steering_bit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.no_pure_steering_bit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:24:18.518803+00:00
-- url     : https://prove2.me/theorems/07200a9e-f8b2-4bb7-b162-856cc3536b43
-- title:
--   No pure steering bit in minimal dimension
-- statement:
--   Consider normalized no-signaling assemblages with a qubit Bob system and two binary inputs and outputs. Call an assemblage pure if every conditional density block has a unit-vector representative, with arbitrary normalized outcome probabilities; its Bob marginal need not be pure. Then
--
--   $$
--   \nexists\,\Psi\ \text{pure such that}\quad
--   \forall\Sigma,\quad \Psi\longrightarrow\Sigma
--   $$
--
--   where \(\Sigma\) ranges over all normalized assemblages with the same minimal dimensions and each arrow denotes an exact single-copy stochastic Bob-to-Alice 1W-LOCC conversion with strictly positive, input-independent success probability. The source may be nonorthogonal. This rules out a universal pure unit of steering in the minimal dimension, while making no assertion about mixed sources.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 7, Theorem 5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Theorem 5, PDF p.7; Appendix F, pp.14–16. No pure source is universal for
normalized targets of the same minimal dimension. The source need not be
orthogonal; no claim about a mixed universal source is made. -/
theorem no_pure_steering_bit :
    ¬ ∃ rho : AssemblageBlocks 2 2 2, IsNormalized rho ∧ IsPureAssemblage rho ∧
      ∀ sigma : AssemblageBlocks 2 2 2, IsNormalized sigma → SteeringConverts rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
