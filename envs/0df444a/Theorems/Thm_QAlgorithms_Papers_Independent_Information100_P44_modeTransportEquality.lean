-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_modeTransportEquality
-- name    : QAlgorithms.Papers.Independent.Information100.P44.modeTransportEquality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:34:51.559144+00:00
-- url     : https://prove2.me/theorems/38e1f9e5-8764-4277-868e-3883fed0569b
-- title:
--   Theorem 3: equality in the TO mode-transport bound
-- statement:
--   Let $\rho$ be a density matrix and $\sigma=\Phi(\rho)$ for a thermal operation with common shell vectors $w_{r|i}$ and transition probabilities $p(r|i)$. For fixed output labels $r,s$, let $S_{rs}$ consist of pairs $(i,j)$ with equal input and output energy gaps, $\rho_{ij}\ne0$, and $p(r|i)p(s|j)>0$. Then
--   $$|\sigma_{rs}|\le\sum_{(i,j)\in S_{rs}}|\rho_{ij}|\sqrt{p(r|i)p(s|j)}.$$
--   Equality holds if and only if each selected pair of shell vectors is complex-collinear and all nonzero numbers $\rho_{ij}\langle w_{s|j},w_{r|i}\rangle$ have one common phase. A common phase means that all these numbers are nonnegative real multiples of one unit complex number. Empty support is allowed and imposes no equality condition. This separates the Cauchy–Schwarz and triangle equality requirements.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 10, Theorem 3: equality in the TO mode-transport bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Theorem 3: upper bound and both equality conditions; empty support is allowed. -/
theorem modeTransportEquality {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) (rho : Mat d)
    (hrho : IsDensityMatrix rho) (r s : Fin d) :
    ‖thermalApply D rho r s‖ ≤ modeBound E (thermalApply D) rho r s ∧
    (‖thermalApply D rho r s‖ = modeBound E (thermalApply D) rho r s ↔
      (∀ a ∈ contributors E (thermalApply D) rho r s,
        Collinear (shellVector D r a.1) (shellVector D s a.2)) ∧
      ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ a ∈ contributors E (thermalApply D) rho r s,
        let t := rho a.1 a.2 * inner ℂ (shellVector D s a.2) (shellVector D r a.1)
        t ≠ 0 → ∃ l : ℝ, 0 ≤ l ∧ t = (l : ℂ) * z) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
