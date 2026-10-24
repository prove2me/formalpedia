-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_maximally_entangled_measured_values
-- name    : QAlgorithms.Papers.Independent.Support50.P16.maximally_entangled_measured_values
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:58:51.21962+00:00
-- url     : https://prove2.me/theorems/523f5297-bda0-4c51-b06f-a9a6bd0d0713
-- title:
--   Proposition 4, Eq. (9): exact value on maximally entangled states
-- statement:
--   For an integer $d\ge1$, let $\Phi_d=|\Phi_d\rangle\langle\Phi_d|$ with $|\Phi_d\rangle=d^{-1/2}\sum_{i=1}^d|i\rangle_A|i\rangle_B$. For a measurement class $\mathcal M$, let $E_{r,\mathcal M}$ be the infimum over separable states of the supremum of the measured classical relative entropy in bits. The classes LO, $1$-LOCC, LOCC, SEP and PPT mean local measurements, measurements with communication from $A$ to $B$, arbitrary two-way local protocols, separable effects, and positive-partial-transpose effects, respectively. Then
--
--   $$
--   E_{r,\mathrm{LO}}(\Phi_d)=E_{r,1\text{-LOCC}}(\Phi_d)=E_{r,\mathrm{LOCC}}(\Phi_d)=E_{r,\mathrm{SEP}}(\Phi_d)=E_{r,\mathrm{PPT}}(\Phi_d)=\log_2(d+1)-1.
--   $$
--
--   The product corner $d=1$ gives zero. This computes the single-copy measured relative entropies exactly.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 5, Proposition 4, Eq. (9): exact value on maximally entangled states

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

/-- Proposition 4, Eq.(9), PDF p.5; proof pp.11--12. The d=1 product is included. -/
theorem maximally_entangled_measured_values (d : ℕ+) :
    ∀ c : MeasurementKind, measuredEntanglement c d d
      (QAlgorithms.Papers.Independent.Dependency50.P19.epr d) =
      ENNReal.ofReal (Real.logb 2 ((d : ℝ)+1) - 1) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
