-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_maximally_entangled_regularization_separations
-- name    : QAlgorithms.Papers.Independent.Support50.P16.maximally_entangled_regularization_separations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:07:14.819802+00:00
-- url     : https://prove2.me/theorems/42891c8c-d0d2-44ef-8602-d576d7461805
-- title:
--   Unnumbered strict separation from regularization on maximally entangled states
-- statement:
--   For an integer $d>1$, let $\Phi_d$ be the normalized rank-$d$ maximally entangled density matrix. Write $E_{r,\leftrightarrow}=E_{r,\mathrm{LOCC}}$ and $E_{r,\to}(\rho)=\sup_{\Lambda\in\mathrm{LOCC}}E_{r,1\text{-LOCC}}(\Lambda(\rho))$, allowing arbitrary finite quantum outputs for $\Lambda$. The grouped-copy regularization limits exist, and
--
--   $$
--   E_{r,\leftrightarrow}(\Phi_d)<E_{r,\leftrightarrow}^\infty(\Phi_d),\qquad
--   E_{r,\to}(\Phi_d)<E_{r,\to}^\infty(\Phi_d).
--   $$
--
--   The $d=1$ product state is excluded because both sides are zero there. These are strict single-copy versus regularized separations.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 16, Unnumbered strict separation from regularization on maximally entangled states

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

/-- Strict regularization separations, PDF p.16. The product corner d=1 is
excluded: it has value zero on both sides, as Proposition 4 implies. -/
theorem maximally_entangled_regularization_separations (d : ℕ+) (hd : 1 < (d : ℕ)) :
    let phi := QAlgorithms.Papers.Independent.Dependency50.P19.epr d
    Regularizes updated phi ∧ Regularizes (measuredEntanglement .LOCC) phi ∧
    measuredEntanglement .LOCC d d phi < regularized (measuredEntanglement .LOCC) phi ∧
    updated d d phi < regularized updated phi := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
