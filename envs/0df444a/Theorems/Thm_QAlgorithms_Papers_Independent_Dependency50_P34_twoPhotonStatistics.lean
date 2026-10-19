-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P34_twoPhotonStatistics
-- name    : QAlgorithms.Papers.Independent.Dependency50.P34.twoPhotonStatistics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:23:14.145983+00:00
-- url     : https://prove2.me/theorems/5010632f-a48c-4d54-9b7a-6d814eada718
-- title:
--   Two-photon comparison probabilities and constant output means
-- statement:
--   Use the balanced Mach–Zehnder interferometer with transmission amplitude $1/\sqrt2$, reflection amplitude $i/\sqrt2$, phase $\theta\in\mathbb R$ in its second intermediate path, and input $|1,1\rangle$. Let $\psi_\theta$ be its output, constructed from the scattering matrix and the two input creation operators. It is normalized, supported on total occupation two, and its occupation probabilities sum to one. Let $N_4,N_5$ denote the measured photon counts at the two outputs. With probabilities defined by squared Fock coefficients and means by convergent occupation sums,
--   $$
--   \Pr(N_4=1,N_5=1)=\cos^2\theta,\qquad
--   \Pr(N_4=2)=\Pr(N_5=2)=\tfrac12\sin^2\theta,
--   $$
--   $$
--   \mathbb E[N_4]=\mathbb E[N_5]=1.
--   $$
--   All probability and first-moment series used here are summable. These formulas describe the comparison with a coherent input of unit mean intensity while retaining the two-photon input's distinct quantum state.
-- source:
--   Quantum Interference between a Single-Photon Fock State and a Coherent State, arXiv:1009.1844v2, PDF p. 8, §III/D, paragraph after Eq.(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Dependency50.P34

/-- arXiv:1009.1844v2, PDF p.8, §III/D, paragraph after Eq.(35).
Coincidence and both two-photon marginal probabilities, and both occupation-sum
means, are calculated from the constructed output. Normalization, fixed total
occupation, and summability are conclusions, never hypotheses. The Eq.(35)
relative-phase correction does not change these probabilities. -/
theorem twoPhotonStatistics (theta : ℝ) :
    let psi := comparisonOutput theta
    ‖psi‖ = 1 ∧
      (∀ nm : ℕ × ℕ, nm.1 + nm.2 ≠ 2 → psi nm = 0) ∧
      Summable (jointWeight psi) ∧
      (∑' nm : ℕ × ℕ, jointWeight psi nm) = 1 ∧
      jointWeight psi (1, 1) = Real.cos theta ^ 2 ∧
      marginalWeight psi 0 2 = (1 / 2 : ℝ) * Real.sin theta ^ 2 ∧
      marginalWeight psi 1 2 = (1 / 2 : ℝ) * Real.sin theta ^ 2 ∧
      (∀ j : Fin 2,
        Summable (fun nm : ℕ × ℕ =>
          if portOccupation j nm = 2 then jointWeight psi nm else 0)) ∧
      (∀ j : Fin 2,
        Summable (fun nm : ℕ × ℕ => (portOccupation j nm : ℝ) * jointWeight psi nm)) ∧
      photonMean psi 0 = 1 ∧ photonMean psi 1 = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P34

end
