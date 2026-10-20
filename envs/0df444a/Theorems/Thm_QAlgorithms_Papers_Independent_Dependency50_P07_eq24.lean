-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_eq24
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.eq24
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:33:34.492199+00:00
-- url     : https://prove2.me/theorems/4e8a5e87-ab0c-4ed5-bee8-308aff03065b
-- title:
--   Total fixed-measurement common randomness and rank-one optimizers
-- statement:
--   Let $\rho^{AB}$ be a density matrix on finite nonzero systems, and let $d=\dim A$. Let $D^{(1)}(\rho,\infty)$ be the supremum over finite nonnegative communication rates of the excess common randomness obtained from one repeated POVM on $A$. Then
--
--   $$D^{(1)}(\rho,\infty)=\max_{M:A\to X}I(X;B)=C_A(\rho),$$
--
--   where $C_A$ is the POVM correlation optimization of Henderson–Vedral [21]. An optimizer exists with at most $d^2$ outcomes and every nonzero effect of rank one; zero effects can be removed. This identifies the one-copy total excess with the cited correlation measure and its finite optimizer restriction.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 15, §3, (24): total fixed-measurement CR and POVM restriction

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

/-- PDF p.15, (24): an optimizer simultaneously has at most dim(A)^2 outcomes and rank-one
nonzero effects. Zero effects may be discarded; padded zero outcomes are allowed here. -/
theorem eq24 (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    fixedTotal rho = classicalCorrelation rho ∧
    ∃ M : Measurement A, M.outcomes ≤ Fintype.card A ^ 2 ∧
      (∀ x, M.effect x ≠ 0 → (M.effect x).rank = 1) ∧
      fixedTotal rho = ensembleInformation (measuredCQ rho M) ∧
      ∀ N : Measurement A, ensembleInformation (measuredCQ rho N) ≤ ensembleInformation (measuredCQ rho M) := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
