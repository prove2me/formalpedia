-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_squashed_commensurate_lower_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P16.squashed_commensurate_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:56:00.660858+00:00
-- url     : https://prove2.me/theorems/d6409f64-3821-472e-b0b1-7ee63baf5d6a
-- title:
--   Theorem 2, Eq. (8): commensurate lower bound for squashed entanglement
-- statement:
--   Let $\rho_{AB}$ be a density matrix on two nonzero finite-dimensional complex registers. Write $E_{\mathrm{sq}}$ for half the infimum of $I(A;B\mid E)$ over every normalized finite-dimensional extension, $E_{r,1\text{-LOCC}}$ for the infimum over separable $\sigma_{AB}$ of the supremum of the classical relative entropy after one-way measurements from $A$ to $B$, and a superscript $\infty$ for the per-copy regularization limit. Entropies use base-two logarithms. Then
--
--   $$
--   E_{\mathrm{sq}}(\rho_{AB})\ge\tfrac12 E_{r,1\text{-LOCC}}^\infty(\rho_{AB})\ge\tfrac12 E_{r,1\text{-LOCC}}(\rho_{AB}).
--   $$
--
--   The regularized quantity is asserted to be an actual limit. This is the paper's commensurate lower bound for squashed entanglement.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 4, Theorem 2, Eq. (8): commensurate lower bound for squashed entanglement

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

/-- Theorem 2, Eq.(8), PDF p.4; proof p.9. Both halves and both inequalities. -/
theorem squashed_commensurate_lower_bound {a b : ℕ+} (rho : Bipartite a b)
    (hrho : IsDensityMatrix rho) :
    Regularizes (measuredEntanglement .oneWay) rho ∧
    regularized (measuredEntanglement .oneWay) rho / 2 ≤ squashed a b rho ∧
    measuredEntanglement .oneWay a b rho / 2 ≤ regularized (measuredEntanglement .oneWay) rho / 2 := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
