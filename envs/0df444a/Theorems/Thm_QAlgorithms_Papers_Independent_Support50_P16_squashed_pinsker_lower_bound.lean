-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_squashed_pinsker_lower_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P16.squashed_pinsker_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:03:05.356162+00:00
-- url     : https://prove2.me/theorems/7d106e42-28ff-4853-bc88-6ff503ea1c66
-- title:
--   Unnumbered improved one-way trace-norm faithfulness bound
-- statement:
--   Let $\rho_{AB}$ be any density matrix on nonzero finite-dimensional registers. Write $\mathrm{SEP}(A:B)$ for finite convex mixtures of product density matrices and $\|\rho-\sigma\|_{1\text{-LOCC}}=\sup_M\|M(\rho)-M(\sigma)\|_1$, where $M$ ranges over normalized one-way measurements from $A$ to $B$. With full classical $\ell_1$ distance, the minimum is attained and
--
--   $$
--   E_{\mathrm{sq}}(\rho_{AB})\ge\frac{1}{4\ln2}\min_{\sigma_{AB}\in\mathrm{SEP}(A:B)}\|\rho_{AB}-\sigma_{AB}\|_{1\text{-LOCC}}^2.
--   $$
--
--   Squashed entanglement is half the infimum of conditional mutual information over all normalized finite-dimensional extensions, in bits. The Lean statement explicitly includes a minimizing separable state. This improves the earlier coefficient $1/(16\ln2)$.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 4, Unnumbered improved one-way trace-norm faithfulness bound

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

/-- Improved unnumbered Pinsker consequence, PDF p.4. The full measured l1 norm
has coefficient 1/(4 ln 2). A minimizing separable state is asserted to exist. -/
theorem squashed_pinsker_lower_bound {a b : ℕ+} (rho : Bipartite a b)
    (hrho : IsDensityMatrix rho) :
    ∃ sigma ∈ separable a b,
      (∀ competitor ∈ separable a b,
        measurementDistance (measurementClass .oneWay a b) rho sigma ^ 2 ≤
        measurementDistance (measurementClass .oneWay a b) rho competitor ^ 2) ∧
      ENNReal.ofReal (measurementDistance (measurementClass .oneWay a b) rho sigma ^ 2 /
        (4 * Real.log 2)) ≤ squashed a b rho := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
