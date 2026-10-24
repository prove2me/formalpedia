-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_relative_entropy_orderings
-- name    : QAlgorithms.Papers.Independent.Support50.P16.relative_entropy_orderings
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:06:13.269314+00:00
-- url     : https://prove2.me/theorems/f8a75f72-09ab-41ea-b936-11f85b59ed85
-- title:
--   Unnumbered orderings and the new distillation chain
-- statement:
--   For a density matrix $\rho_{AB}$ on nonzero finite-dimensional registers, write $E_d$ for the operational two-way LOCC distillation rate and $E_c$ for the infimum of eventual LOCC formation rates from shared singlets, with vanishing full trace-norm error. Let $E_r$ be ordinary relative entropy of entanglement, $E_{r,\leftrightarrow}=E_{r,\mathrm{LOCC}}$, and $E_{r,\to}$ its one-way measured version optimized after arbitrary LOCC operations with finite quantum outputs. All rates use bits per input copy. The regularizations are actual limits, and
--
--   $$
--   E_d\le E_{r,\to}^\infty\le E_{r,\leftrightarrow}^\infty\le E_r^\infty\le E_c,
--   \qquad E_{r,\to}\le E_{r,\leftrightarrow}.
--   $$
--
--   All terms are evaluated at $\rho_{AB}$. The endpoint comparison with $E_c$ is cited background in the source; the new chain includes Proposition 7.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 13, Unnumbered orderings and the new distillation chain

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

/-- Unnumbered ordering chain, PDF p.13. E_c is operational formation cost.
The last clause retains the single-copy update ordering used on p.15. -/
theorem relative_entropy_orderings {a b : ℕ+} (rho : Bipartite a b)
    (hrho : IsDensityMatrix rho) :
    Regularizes updated rho ∧ Regularizes (measuredEntanglement .LOCC) rho ∧ Regularizes relative rho ∧
    distillable a b rho ≤ regularized updated rho ∧
    regularized updated rho ≤ regularized (measuredEntanglement .LOCC) rho ∧
    regularized (measuredEntanglement .LOCC) rho ≤ regularized relative rho ∧
    regularized relative rho ≤ cost a b rho ∧ updated a b rho ≤ measuredEntanglement .LOCC a b rho := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
