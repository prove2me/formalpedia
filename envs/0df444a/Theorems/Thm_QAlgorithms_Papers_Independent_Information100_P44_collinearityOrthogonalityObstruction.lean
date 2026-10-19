-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_collinearityOrthogonalityObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P44.collinearityOrthogonalityObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:36:06.81671+00:00
-- url     : https://prove2.me/theorems/7df82788-ecee-434c-8ba9-bff7b0b596b5
-- title:
--   Proposition 1: collinearity–orthogonality obstruction
-- statement:
--   Fix basis energies, a real inverse temperature, an input density matrix $\rho$, target coarse energy populations, a fixed basis transition matrix $P$, and selected elementary bounds. Suppose every jointly saturating thermal dilation realizing these data forces two designated shell vectors to be nonzero and complex-collinear. Suppose also that every finite nonempty bath dilation realizing the required task and transition data satisfies orthogonality for those same designated vectors. Then
--   $$\nexists\Phi\in\mathrm{TO}_{\rm fin}\quad\Phi\text{ realizes the task and }P\text{ and saturates all selected bounds}.$$
--   Both premises quantify over every admissible finite bath and common energy-preserving unitary. This is a conditional obstruction, not an unconditional impossibility claim about the chosen task.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 11, Proposition 1: collinearity–orthogonality obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.11, Proposition 1: orthogonality must hold for every finite-bath realization. -/
theorem collinearityOrthogonalityObstruction {d : ℕ} (hd : 0 < d)
    (E : Fin d → ℝ) (beta : ℝ) (rho : Mat d) (hrho : IsDensityMatrix rho)
    (pf : ℝ → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (edges : TransferEdges d)
    (u v : Fin d × Fin d)
    (hrequires : ∀ (b : ℕ) (D : ThermalDilation E beta b),
      PopulationTask E rho pf (thermalApply D) →
      (∀ r i, population (thermalApply D) r i = P r i) →
      JointElementary (thermalApply D) edges →
      shellVector D u.1 u.2 ≠ 0 ∧ shellVector D v.1 v.2 ≠ 0 ∧
      Collinear (shellVector D u.1 u.2) (shellVector D v.1 v.2))
    (horthogonal : ∀ (b : ℕ) (D : ThermalDilation E beta b),
      PopulationTask E rho pf (thermalApply D) →
      (∀ r i, population (thermalApply D) r i = P r i) →
      inner ℂ (shellVector D v.1 v.2) (shellVector D u.1 u.2) = 0) :
    ¬ ∃ Phi : Map d, IsFiniteThermal E beta Phi ∧ PopulationTask E rho pf Phi ∧
      (∀ r i, population Phi r i = P r i) ∧ JointElementary Phi edges := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
