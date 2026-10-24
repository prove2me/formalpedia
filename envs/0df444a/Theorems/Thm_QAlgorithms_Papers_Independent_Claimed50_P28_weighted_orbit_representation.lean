-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_weighted_orbit_representation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.weighted_orbit_representation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:29:30.244913+00:00
-- url     : https://prove2.me/theorems/0d3e2b5d-6d90-4b6a-8206-19d40dc98357
-- title:
--   Independent unitary preparation and observable orbits give block-scalar G
-- statement:
--   For d≥2, a density matrix ρ, an operator A, and independent normalized SU(d) Haar variables U,V, put G=∫|UAU†⊗(VρV†)^T⟩⟩⟨⟨UAU†⊗(VρV†)^T| dU dV. Then G is positive and G=∑_(j=1)^4 g_j P_j for nonnegative real g_j, using the four paired-wire projectors from (28). The transpose on the input factor is the output-first Choi convention. A ranges over generic operators, as in the source’s (2),(9); Hermitian observables are included.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 4, Sentence after (37)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.4, sentence after (37): independent unitary input and observable orbits
produce precisely a positive block-scalar representation in the four sectors. -/
theorem weighted_orbit_representation {d : ℕ} (hd : 2 ≤ d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (rho A : Op (Fin d)) (hrho : QAlgorithms.IsDensityMatrix rho) :
    (orbitRepresentation haar rho A).PosSemidef ∧
    ∃ g : Fin 4 → ℝ, (∀ j, 0 ≤ g j) ∧
      orbitRepresentation haar rho A = ∑ j, (g j : ℂ) • sector d j := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
