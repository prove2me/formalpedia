-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_pure_state_regularized_values
-- name    : QAlgorithms.Papers.Independent.Support50.P16.pure_state_regularized_values
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:00:24.669177+00:00
-- url     : https://prove2.me/theorems/7885ca5f-33fe-427a-9ea2-abe571bafaee
-- title:
--   Unnumbered pure-state corollary of Proposition 4, Eq. (10)
-- statement:
--   Let $\psi_{AB}$ be a normalized pure-state density matrix on nonzero finite-dimensional registers, and let $S(\psi_A)=-\operatorname{Tr}\psi_A\log_2\psi_A$ with $\psi_A=\operatorname{Tr}_B\psi_{AB}$. For each measurement class $\mathcal M\in\{\mathrm{LO},1\text{-LOCC},\mathrm{LOCC},\mathrm{SEP},\mathrm{PPT}\}$, define $E_{r,\mathcal M}$ by minimizing the optimized measured relative entropy over separable states; one-way communication is from $A$ to $B$. Then the following actual limits exist:
--
--   $$
--   \lim_{n\to\infty}\frac1n E_{r,\mathcal M}(\psi_{AB}^{\otimes n})=E_{r,\mathcal M}^\infty(\psi_{AB})=S(\psi_A)
--   \quad\text{for every such }\mathcal M.
--   $$
--
--   Each laboratory holds all its copies. The LO case is included; no equality between the single-copy value and the marginal entropy is asserted.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 5, Unnumbered pure-state corollary of Proposition 4, Eq. (10)

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

/-- Pure-state corollary, Eq.(10), PDF p.5; proof pp.12--13.
This asserts the actual limits for all five classes, including LO. -/
theorem pure_state_regularized_values {a b : ℕ+} (rho : Bipartite a b)
    (hrho : IsDensityMatrix rho)
    (hpure : QAlgorithms.Papers.Independent.Information100.P08.IsPure rho) :
    ∀ c : MeasurementKind, Regularizes (measuredEntanglement c) rho ∧
      regularized (measuredEntanglement c) rho = ENNReal.ofReal (vnEntropy (traceRight rho)) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
