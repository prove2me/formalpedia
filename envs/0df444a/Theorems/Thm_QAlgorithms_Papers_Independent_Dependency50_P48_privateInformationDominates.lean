-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_privateInformationDominates
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.privateInformationDominates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:40:40.809191+00:00
-- url     : https://prove2.me/theorems/0c45adb1-e1bf-4168-981e-b010229b71b4
-- title:
--   Private information dominates coherent information
-- statement:
--   Let $\mathcal N$ be a finite-dimensional quantum channel with a fixed isometric dilation into finite nonempty registers $Q\otimes E$, with the entire complementary register included in $E$. Let $\rho$ be a positive semidefinite trace-one input density matrix. With entropies measured in bits and $I_p$ defined by minimization over all finite mixed-state decompositions of $\rho$,
--
--   $$I_p(\rho,\mathcal N)\ge I_c(\rho,\mathcal N).$$
--
--   This compares the single-input private and coherent information quantities, without assuming any property of an optimizing decomposition.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 9, Unnumbered inequality after (31)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Inequality after (31), PDF p.9. Pure decomposition and vanishing component
coherent information are proved content, not assumptions of this statement. -/
theorem privateInformationDominates [Nonempty P] [Nonempty Q] [Nonempty E]
    (U : Matrix (Q × E) P ℂ) (hU : IsDilation U)
    (rho : Matrix P P ℂ) (hrho : IsDensityMatrix rho) :
    coherentInformation (receiver U) rho ≤ privateInformation U rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
