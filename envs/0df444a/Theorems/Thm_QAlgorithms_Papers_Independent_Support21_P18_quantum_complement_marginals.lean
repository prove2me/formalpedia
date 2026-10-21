-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_quantum_complement_marginals
-- name    : QAlgorithms.Papers.Independent.Support21.P18.quantum_complement_marginals
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:50:20.33699+00:00
-- url     : https://prove2.me/theorems/e8a60729-3bd7-4179-9ff9-cf30ed4b35b0
-- title:
--   Individual quantum-output complements
-- statement:
--   Let $N,M\ge1$ and $\psi$ be any unit qubit vector. Let $q_{NM}(\psi)$ be the joint output of Eqs. (7),(8), using $\gamma_j=(-1)^j\sqrt{\binom{N+M-j}{N}/\binom{N+M+1}{M}}$ and the fixed complement phase convention of Eq. (1). Discard the $N+M$ clone sites and retain any one of the $M$ complement sites. Its reduced density is
--   $$
--   \rho_{c_i}=\frac N{N+2}(I-|\psi\rangle\langle\psi|)+\frac1{N+2}I.
--   $$
--   It equals the single-output measurement-based density on the same coherent input, and its overlap with $I-|\psi\rangle\langle\psi|$ is $(N+1)/(N+2)$.
--
--   This identifies each individual complement, independently of the number produced; the assertion concerns reduced densities.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 3, Quantum scenario after Eq.(8): individual quantum-output complements

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3 after Eq.(8): all individual complemented outputs have Eq.(6),
independently of their number. This is an equality of marginals, not a product claim. -/
theorem quantum_complement_marginals (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : IsState psi) :
    ∀ i : Fin M,
      siteReduction (quantumComplements N M psi) i = complementOutput N psi ∧
      siteReduction (quantumComplements N M psi) i =
        measurementNot N (pureDensity (symmetricQubitKet N psi)) ∧
      effectProb (orthogonalDensity psi) (siteReduction (quantumComplements N M psi) i) =
        ((N : ℝ) + 1) / (N + 2) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
