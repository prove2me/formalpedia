-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P12_maximally_mixed_qubit_extreme_iff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P12.maximally_mixed_qubit_extreme_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:51:04.037752+00:00
-- url     : https://prove2.me/theorems/e95df582-5b19-4851-8e24-1cbec8b7e39c
-- title:
--   Theorem 3.1: extreme qubit couplings with maximally mixed marginals
-- statement:
--   Use the fixed computational basis $|0\rangle,|1\rangle$ in the first copy of $\mathbb C^2$. Let $\rho$ be a density matrix on $\mathbb C^2\otimes\mathbb C^2$ with both marginals $I_2/2$, and write $C(I_2/2,I_2/2)$ for all such states. Then
--   $$\rho\in\operatorname{Ext}_{\mathbb R}C(I_2/2,I_2/2)\quad\Longleftrightarrow\quad\exists\text{ an orthonormal basis }(\psi_0,\psi_1)\text{ of }\mathbb C^2:\ \rho=|\Omega\rangle\langle\Omega|,$$
--   where the vector is constructed from that basis by
--   $$|\Omega\rangle=\frac{|0\rangle\otimes|\psi_0\rangle+|1\rangle\otimes|\psi_1\rangle}{\sqrt2}.$$
--   Thus the extreme couplings with these marginals are exactly the indicated maximally entangled pure states. The basis is allowed to be complex, and the density-matrix equality is insensitive to global phase.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, PDF p. 9, Theorem 3.1: extreme qubit couplings with both marginals I/2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- Theorem 3.1, PDF p.9, completed PDF pp.12–13. Density equality absorbs global phase.
The basis witness is genuinely orthonormal over C. Omega is constructed from it.
The proof's rank-two contradiction is not an assumption. -/
theorem maximally_mixed_qubit_extreme_iff
    (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hmem : rho ∈ finiteCouplingSet ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) :
    rho ∈ Set.extremePoints ℝ
      (finiteCouplingSet ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) ↔
      ∃ psi : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)),
        rho = pureDensity (omegaFromBasis psi) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P12
