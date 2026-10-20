-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_theorem11
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.theorem11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:37:34.803465+00:00
-- url     : https://prove2.me/theorems/453e30f7-3b97-469b-8a56-da6d413aed97
-- title:
--   Additivity of total fixed-measurement CR with a pure factor
-- statement:
--   Let $|\psi\rangle\in A\otimes B$ be a unit vector, let $\rho=|\psi\rangle\langle\psi|$, and let $\sigma^{A'B'}$ be any density matrix on finite nonzero systems. Regroup the product across $AA':BB'$. Then
--
--   $$D^{(1)}(\rho\otimes\sigma,\infty)=D^{(1)}(\rho,\infty)+D^{(1)}(\sigma,\infty).$$
--
--   The total fixed-measurement excess is defined operationally with noiseless one-way communication. The second factor may be mixed or entangled. This extends the pure-product example to an arbitrary second factor.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 17, Theorem 11: additivity with a pure factor

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

/-- PDF pp.17--18, Theorem 11: a pure normalized first factor and an arbitrary mixed or
entangled second density matrix. The proof's entropy inequality (26) is not a hypothesis. -/
theorem theorem11 (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi)
    (sigma : Matrix (A2 × B2) (A2 × B2) ℂ) (hsigma : IsDensityMatrix sigma) :
    fixedTotal (bipartiteProduct (pureDensity psi) sigma) =
      fixedTotal (pureDensity psi) + fixedTotal sigma := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
