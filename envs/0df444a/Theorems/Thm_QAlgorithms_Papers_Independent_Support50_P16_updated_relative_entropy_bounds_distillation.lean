-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_updated_relative_entropy_bounds_distillation
-- name    : QAlgorithms.Papers.Independent.Support50.P16.updated_relative_entropy_bounds_distillation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:05:05.379008+00:00
-- url     : https://prove2.me/theorems/e0ec007c-ebf6-4e9e-9376-11d5012c1a39
-- title:
--   Proposition 7: distillable entanglement lower bound
-- statement:
--   Let $\rho_{AB}$ be any normalized finite-dimensional bipartite state with nonzero local dimensions. Let $E_d$ be its operational two-way LOCC distillable entanglement: the supremum of asymptotically achievable rates $\log_2 d_n/n$ of normalized rank-$d_n$ maximally entangled targets, with vanishing full trace-norm error for all sufficiently large positive block lengths. Let $E_{r,\to}$ be the supremum, over LOCC operations with arbitrary finite quantum outputs, of one-way measured relative entropy of entanglement. Its regularization limit exists and
--
--   $$
--   E_{r,\to}^\infty(\rho_{AB})\ge E_d(\rho_{AB}).
--   $$
--
--   The supremum need not be attained by an optimum protocol sequence. This relates a measured-relative-entropy quantity to an operational distillation rate.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 14, Proposition 7: distillable entanglement lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16

namespace QAlgorithms.Papers.Independent.Support50.P16

noncomputable section

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "tau" => QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed

local notation "RE" => QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement

local notation "RER" => QAlgorithms.Papers.Independent.Information100.P54.regularizedEntanglement

local notation "SQ" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "CMI" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "MI" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "LOCC" => QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC

local notation "power" => QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower

local notation "index" => QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex

-- Accepted matrix coordinates (not P50.Bipartite, which is a vector space).

local notation "Bipartite" => QAlgorithms.Papers.Independent.Dependency50.P50.BipartiteMat

-- Positive outcome counts follow already from a POVM on a nonzero register.

local notation "FiniteMeasurement" => QAlgorithms.Papers.Independent.Information100.P04.Measurement

local notation "relative" =>
  ((fun _ _ rho => RE rho) : ExtendedEntanglementFunctional)

-- Reuse the accepted operational/variational quantity through a typed notation.

local notation "squashed" =>
  ((fun _ _ rho => ENNReal.ofReal (SQ rho)) : ExtendedEntanglementFunctional)

local notation "originalMarginal" => QAlgorithms.Papers.Independent.Information100.P04.principalMarginal

-- Exact accepted partial trace of the same AA'BB' extension.

local notation "ancillaryMarginal" => QAlgorithms.Papers.Independent.Information100.P04.ancillaryMarginal

local notation "distillable" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Gap48.P32.twoWayDistillable rho)) : ExtendedEntanglementFunctional)

local notation "cost" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Dependency50.P42.alternativeCost
    (fun _ _ X Y => traceNorm (X-Y)) rho)) : ExtendedEntanglementFunctional)

/-- Proposition 7, PDF p.14; proof pp.14--15. E_d is operational two-way LOCC. -/
theorem updated_relative_entropy_bounds_distillation {a b : ℕ+} (rho : Bipartite a b)
    (hrho : IsDensityMatrix rho) :
    Regularizes updated rho ∧ distillable a b rho ≤ regularized updated rho := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
