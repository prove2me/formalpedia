-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_proposition_3_2
-- name    : QAlgorithms.Papers.Independent.Information100.P50.proposition_3_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:54:51.87226+00:00
-- url     : https://prove2.me/theorems/bd65b8fd-4936-46b6-99fa-d71e24b1118a
-- title:
--   Proposition 3.2: For every nonzero finite input space X and output space of dimension ≥2, there exist CP Phi1,Psi1,Phi2,Psi2 wi
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For every positive input dimension and output dimension at least two there exist four CP maps with
--
--   $$\Phi_1+\Psi_1=\Phi_2+\Psi_2,\qquad \widehat F(\Phi_1,\Psi_1)=0,\qquad \widehat F(\Phi_2,\Psi_2)=1.$$
--
--   The fidelity is unsquared and uses a common bipartite density input. The maps are chosen after the dimensions. This exhibits opposite fidelities among splittings of the same CP map.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 10, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Proposition 3.2, source PDF pp.10–11. Dimensions precede the existential maps. -/
theorem proposition_3_2 {dx dy : ℕ} (hdx : 0 < dx) (hdy : 2 ≤ dy) :
    ∃ Phi1 Psi1 Phi2 Psi2 : Lin dx dy,
      Entanglement.IsCompletelyPositive Phi1 ∧ Entanglement.IsCompletelyPositive Psi1 ∧
      Entanglement.IsCompletelyPositive Phi2 ∧ Entanglement.IsCompletelyPositive Psi2 ∧
      Phi1 + Psi1 = Phi2 + Psi2 ∧ geometricFidelity Phi1 Psi1 = 0 ∧
      geometricFidelity Phi2 Psi2 = 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
