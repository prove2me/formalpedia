-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_separableTotal
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.separableTotal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:35:58.440906+00:00
-- url     : https://prove2.me/theorems/a646b726-d298-4f3d-9c78-cb2cef53fb4b
-- title:
--   Operational single-letterization for separable states
-- statement:
--   Let $\rho^{AB}$ be a separable density matrix on finite nonzero systems, and let $L\ge1$ be an integer. In the one-way common-randomness model, define total excess as the supremum over finite nonnegative communication rates. The unrestricted, fixed-$L$-block, and fixed-one-copy quantities obey
--
--   $$D(\rho,\infty)=D^{(L)}(\rho,\infty)=D^{(1)}(\rho,\infty).$$
--
--   Block quantities are normalized per original copy. This is the operational consequence of separable-factor additivity at unlimited communication; it gives no finite-rate single-letterization.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 16, §3, consequence of Theorem 9: separable single-letterization

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

/-- PDF p.16, consequence of Theorem 9: separable operational single-letterization. -/
theorem separableTotal (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (hsep : QAlgorithms.Entanglement.IsSeparableDensity rho) (L : ℕ) (hL : 0 < L) :
    total rho = blockTotal rho L ∧ blockTotal rho L = fixedTotal rho := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
