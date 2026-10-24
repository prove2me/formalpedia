-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_entanglement_comparisons
-- name    : QAlgorithms.Papers.Independent.Support50.P16.entanglement_comparisons
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:04:11.765993+00:00
-- url     : https://prove2.me/theorems/1337d5f5-5e93-4873-8e71-f12bec7edab3
-- title:
--   Proposition 6: comparison of squashed-type and relative-entropy measures
-- statement:
--   Let $\rho_{AB}$ be a density matrix on nonzero finite-dimensional registers. Let $E_{\mathrm{sq}}$ denote quantum squashed entanglement, $E_{\mathrm{sq},c}$ its restriction to classical flagged extensions, and $E_I=\tfrac12\inf[I(AA';BB')-I(A';B')]$ over normalized extensions of $\rho_{AB}$ with unrestricted finite $A',B'$. Write $E_r$ for relative entropy of entanglement, $E_{r,\leftrightarrow}=E_{r,\mathrm{LOCC}}$, and $E_{r,\to}(\rho)=\sup_{\Lambda\in\mathrm{LOCC}}E_{r,1\text{-LOCC}}(\Lambda(\rho))$, where $\Lambda$ has arbitrary finite quantum outputs. All entropies are in bits. The regularization limits exist, and
--
--   $$
--   \begin{aligned}
--   2E_{\mathrm{sq},c}^\infty&\ge E_r^\infty,&2E_I&\ge E_{r,\leftrightarrow}^\infty,&2E_{\mathrm{sq}}&\ge E_{r,\to}^\infty,\\
--   2E_{\mathrm{sq},c}&\ge E_r,&2E_I&\ge E_{r,\leftrightarrow},&2E_{\mathrm{sq}}&\ge E_{r,\to}.
--   \end{aligned}
--   $$
--
--   Every quantity is evaluated at $\rho_{AB}$. This retains all three nonregularized versions as well as the three displayed comparisons.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 13, Proposition 6: comparison of squashed-type and relative-entropy measures

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

/-- Proposition 6, PDF pp.13--14: all three comparisons, and ALL three
nonregularized versions. Only E_sq,c is regularized on the left. -/
theorem entanglement_comparisons {a b : ℕ+} (rho : Bipartite a b)
    (hrho : IsDensityMatrix rho) :
    Regularizes classicalSquashed rho ∧ Regularizes relative rho ∧
    Regularizes (measuredEntanglement .LOCC) rho ∧ Regularizes updated rho ∧
    regularized relative rho ≤ 2 * regularized classicalSquashed rho ∧
    regularized (measuredEntanglement .LOCC) rho ≤ 2 * conditionalEntanglement a b rho ∧
    regularized updated rho ≤ 2 * squashed a b rho ∧
    relative a b rho ≤ 2 * classicalSquashed a b rho ∧
    measuredEntanglement .LOCC a b rho ≤ 2 * conditionalEntanglement a b rho ∧
    updated a b rho ≤ 2 * squashed a b rho := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
