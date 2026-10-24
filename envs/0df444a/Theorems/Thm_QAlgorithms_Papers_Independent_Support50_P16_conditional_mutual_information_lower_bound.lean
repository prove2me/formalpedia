-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_conditional_mutual_information_lower_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P16.conditional_mutual_information_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:02:17.468162+00:00
-- url     : https://prove2.me/theorems/acb72ead-5f5b-4a0b-8c2d-f3d142c2e70d
-- title:
--   Unnumbered strengthening of SSA, Eq. (37)
-- statement:
--   For any density matrix $\rho_{ABE}$ on nonzero finite-dimensional registers, let $I(A;B\mid E)_\rho=S(\rho_{AE})+S(\rho_{BE})-S(\rho_E)-S(\rho_{ABE})$, with entropies in bits and actual partial traces. Let $E_{r,1\text{-LOCC}}$ be the relative entropy distance to separable states after optimization over one-way measurements from $A$ to $B$, and let its superscript $\infty$ mean the actual grouped-copy regularization limit. Then
--
--   $$
--   I(A;B\mid E)_\rho\ge E_{r,1\text{-LOCC}}^\infty(\rho_{AB}),\qquad
--   I(A;B\mid E)_\rho\ge E_{r,1\text{-LOCC}}(\rho_{AB}).
--   $$
--
--   The regularization limit exists. This strengthens strong subadditivity without assuming the state is Markov, separable, or pure.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 9, Unnumbered strengthening of SSA, Eq. (37)

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

/-- Eq.(37), PDF p.9, and its unregularized consequence on p.4.
No Markov, purity, or separability hypothesis is imposed. -/
theorem conditional_mutual_information_lower_bound {a b e : ℕ+}
    (rho : Matrix ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ))
      ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) :
    Regularizes (measuredEntanglement .oneWay) (traceRight rho) ∧
    regularized (measuredEntanglement .oneWay) (traceRight rho) ≤ ENNReal.ofReal (CMI rho) ∧
    measuredEntanglement .oneWay a b (traceRight rho) ≤ ENNReal.ofReal (CMI rho) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
