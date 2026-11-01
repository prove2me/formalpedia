-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_nonPauli_resourceNecessary
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.nonPauli_resourceNecessary
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:53:46.660238+00:00
-- url     : https://prove2.me/theorems/0362629b-4e67-4cdb-85ad-33d901a1eabd
-- title:
--   Necessary resource condition for non-Pauli simulation
-- statement:
--   Let $\tau$ be a normalized two-qubit density matrix and fix any conditional stochastic law in the noisy Bell/Pauli protocol. Write $b_i=\operatorname{Tr}[(I\otimes\sigma_i)\tau]$ for Bob's local Bloch vector and $T_{ij}=\operatorname{Tr}[(\sigma_i\otimes\sigma_j)\tau]$ for its correlations. If the simulated channel is not a normalized mixture of Pauli conjugations, then
--
--   $$b\ne0\quad\text{or}\quad\exists i\ne j:\ T_{ij}\ne0.$$
--
--   Moreover $\tau\ne(\mathrm{id}\otimes P)(|\Phi^+\rangle\langle\Phi^+|)$ for every Pauli channel $P$. This necessary condition constrains Bob's vector, and imposes no condition on Alice's local Bloch vector.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 6, Corollary 13

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF p.6, Corollary 13: Bob's vector or off-diagonal
correlations are necessary; also excludes every normalized Pauli Choi resource. -/
theorem nonPauli_resourceNecessary (tau : ResourceOp) (htau : IsDensityMatrix tau)
    (p : Fin 4 → Fin 4 → ℝ) (hp : ClassicalTeleportationLaw p)
    (hnon : ¬ IsPauli (noisyTeleport tau p)) :
    (bobVector tau ≠ 0 ∨ ∃ i j : Fin 3, i ≠ j ∧ resourcePauliCorrelation tau i j ≠ 0) ∧
    ∀ w : Fin 4 → ℝ, FourOutcomeLaw w → tau ≠ normalizedQubitChoi (pauliMixture w) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
