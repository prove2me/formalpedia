-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_theorem9
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.theorem9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:35:26.113017+00:00
-- url     : https://prove2.me/theorems/bec2eab0-aabf-4c29-a0c8-439375b3c3be
-- title:
--   Additivity of total fixed-measurement CR with a separable factor
-- statement:
--   Let $\rho^{AB}$ be a separable density matrix and let $\sigma^{A'B'}$ be any density matrix, on finite nonzero systems. Separability means a finite convex combination of product density matrices. Regroup $\rho\otimes\sigma$ across $AA':BB'$. Then
--
--   $$D^{(1)}(\rho\otimes\sigma,\infty)=D^{(1)}(\rho,\infty)+D^{(1)}(\sigma,\infty).$$
--
--   Here $D^{(1)}(\cdot,\infty)$ is the total operational excess under one repeated measurement and one-way communication. Only the first factor is required to be separable, and no finite-rate additivity is asserted.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 16, Theorem 9: additivity with a separable factor

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section QuantumStatements

variable {A B A2 B2 : Type} [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
  [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
  [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]

/-- PDF pp.16--17, Theorem 9: separability only of the first factor, at unlimited communication. -/
theorem theorem9 (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix (A2 × B2) (A2 × B2) ℂ)
    (hrho : IsDensityMatrix rho) (hsep : QAlgorithms.Entanglement.IsSeparableDensity rho)
    (hsigma : IsDensityMatrix sigma) :
    fixedTotal (bipartiteProduct rho sigma) = fixedTotal rho + fixedTotal sigma := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
