-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_classical_quantum_squashed_separation
-- name    : QAlgorithms.Papers.Independent.Support50.P16.classical_quantum_squashed_separation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:18:49.266239+00:00
-- url     : https://prove2.me/theorems/65e0c440-7db7-4676-af6a-b6bed78d063a
-- title:
--   Unnumbered inequivalence of classical and quantum squashed entanglement
-- statement:
--   Let $E_{\mathrm{sq}}$ be half the infimum of conditional mutual information over every normalized finite-dimensional extension, and let $E_{\mathrm{sq},c}$ restrict the extension to a finite classical flag with possibly mixed conditional states. Entropies use bits. There exist finite nonzero-dimensional bipartite density matrices witnessing each of
--
--   $$
--   E_{\mathrm{sq},c}^\infty(\rho)>E_{\mathrm{sq}}(\rho),\qquad
--   E_{\mathrm{sq},c}(\sigma)>E_{\mathrm{sq}}(\sigma).
--   $$
--
--   The two witnesses may differ, as may their local dimensions, and the regularization is an actual limit. This refutes equality of classical and quantum squashed entanglement. No numerical growth rate is assigned to the phrase “much larger.”
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 16, Unnumbered inequivalence of classical and quantum squashed entanglement

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

/-- Unnumbered classical/quantum squashed separation, PDF p.16.
Two existential witnesses are allowed; no quantitative growth rate is invented. -/
theorem classical_quantum_squashed_separation :
    StrictSeparation (fun _ _ rho => regularized classicalSquashed rho) squashed ∧
    StrictSeparation classicalSquashed squashed := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
