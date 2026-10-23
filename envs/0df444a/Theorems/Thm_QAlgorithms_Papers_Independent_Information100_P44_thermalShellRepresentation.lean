-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_thermalShellRepresentation
-- name    : QAlgorithms.Papers.Independent.Information100.P44.thermalShellRepresentation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:32:43.003119+00:00
-- url     : https://prove2.me/theorems/332e94ad-5b3c-4e49-a379-a70cfbd328f3
-- title:
--   Theorem 2: energy-resolved thermal-operation representation
-- statement:
--   Let a nonzero finite-dimensional system have fixed basis energies $E_i$. Fix a real inverse temperature $\beta$, a nonempty finite bath with energies $\epsilon_\mu$ and normalized Gibbs weights $q_\mu$, and one unitary $U$ preserving total energy. Let $\Phi$ be the thermal channel and define, in the common bath-pair Hilbert space,
--   $$w_{r|i}(\mu,\nu)=\begin{cases}\sqrt{q_\mu}\,U_{(r,\nu),(i,\mu)},&E_i+\epsilon_\mu=E_r+\epsilon_\nu,\\0,&\text{otherwise}.\end{cases}$$
--   Then $p(r|i)=\|w_{r|i}\|^2$. Whenever $E_i-E_j=E_r-E_s$,
--   $$\Phi(|i\rangle\langle j|)_{rs}=\langle w_{s|j},w_{r|i}\rangle,\qquad |\Phi(|i\rangle\langle j|)_{rs}|^2\le p(r|i)p(s|j).$$
--   When the product is positive, equality holds exactly when the two shell vectors are complex-collinear. This representation retains one common energy-preserving dilation.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 7, Theorem 2: energy-resolved thermal-operation representation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.7–8, Theorem 2: one common energy-resolved finite-bath representation. -/
theorem thermalShellRepresentation {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) :
    (∀ r i, population (thermalApply D) r i = ‖shellVector D r i‖ ^ 2) ∧
    (∀ i j r s, E i - E j = E r - E s →
      thermalApply D (matrixUnit i j) r s = inner ℂ (shellVector D s j) (shellVector D r i)) ∧
    (∀ i j r s, E i - E j = E r - E s →
      ‖thermalApply D (matrixUnit i j) r s‖ ^ 2 ≤
        population (thermalApply D) r i * population (thermalApply D) s j) ∧
    (∀ i j r s, E i - E j = E r - E s →
      0 < population (thermalApply D) r i * population (thermalApply D) s j →
      (‖thermalApply D (matrixUnit i j) r s‖ ^ 2 =
        population (thermalApply D) r i * population (thermalApply D) s j ↔
          Collinear (shellVector D r i) (shellVector D s j))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
