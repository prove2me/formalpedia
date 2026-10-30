-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_bellDifferenceSampling
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.bellDifferenceSampling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:55:47.134336+00:00
-- url     : https://prove2.me/theorems/cab48041-d4ed-434f-8da8-4f8ed4886bd6
-- title:
--   Bell difference sampling
-- statement:
--   Let $|\psi\rangle$ be an arbitrary normalized, possibly complex state of $n$ qubits. Write $p_\psi(x)=2^{-n}|\langle\psi|W_x|\psi\rangle|^2$ for its characteristic distribution, and $\Pi_a$ for the four-copy Bell difference measurement outcome $a$. For every phase-space label $a$, the outcome probability is the convolution below. If $\psi$ is a stabilizer state, it equals $p_\psi(a)$.
--
--   $$
--   \operatorname{tr}(\Pi_a\psi^{\otimes4})=\sum_xp_\psi(x)p_\psi(x+a).
--   $$
--
--   This gives the source's bell difference sampling in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 19, theorem-3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.19, Theorem 3.2: arbitrary complex pure states and the stabilizer specialization. -/
theorem bellDifferenceSampling (n : ℕ) (v : EuclideanSpace ℂ (ResidueRegister 2 n))
    (hv : ‖v‖ = 1) (a : DiscretePhaseSpace 2 n) :
    QAlgorithms.effectProb (bellDifference n a) (tensorPower 4 (QAlgorithms.pureDensity v)) =
      ∑ x : DiscretePhaseSpace 2 n, characteristicDistribution v x * characteristicDistribution v (x + a) ∧
    (IsStabilizer v →
      QAlgorithms.effectProb (bellDifference n a) (tensorPower 4 (QAlgorithms.pureDensity v)) =
        characteristicDistribution v a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
