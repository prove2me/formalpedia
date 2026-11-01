-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P12_two_qubit_extremal_rank
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P12.two_qubit_extremal_rank
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:50:34.296241+00:00
-- url     : https://prove2.me/theorems/a32d61be-67cb-46b0-a0ec-286acfa89f7d
-- title:
--   Arbitrary qubit marginals: extreme couplings have rank one or two
-- statement:
--   Let $\rho_1,\rho_2$ be arbitrary density matrices on $\mathbb C^2$. Let $C(\rho_1,\rho_2)$ contain all joint density matrices on $\mathbb C^2\otimes\mathbb C^2$ with those partial traces. Every real convex extreme point $\rho$ of this set satisfies
--   $$\operatorname{rank}\rho\in\{1,2\}.$$
--   This specializes the general bound $\sqrt7$ to two qubits; trace one excludes rank zero. The marginals need not be maximally mixed.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, PDF p. 9, Unnumbered rank-1-or-2 consequence for arbitrary qubit marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- Section 3, PDF pp.8–9: arbitrary qubit marginals, before specializing to I/2. -/
theorem two_qubit_extremal_rank (rho1 rho2 : Matrix (Fin 2) (Fin 2) ℂ)
    (hm1 : IsDensityMatrix rho1) (hm2 : IsDensityMatrix rho2)
    (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hext : rho ∈ Set.extremePoints ℝ (finiteCouplingSet rho1 rho2)) :
    rho.rank = 1 ∨ rho.rank = 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P12
