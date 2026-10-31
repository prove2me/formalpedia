-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_qubit_teleportation_unbounded_outcomes
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.qubit_teleportation_unbounded_outcomes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:36:51.012503+00:00
-- url     : https://prove2.me/theorems/14814845-96f1-4d6d-bfd9-1524e8a8e223
-- title:
--   §2 Remark: arbitrarily many qubit teleportation outcomes
-- statement:
--   For every natural threshold $N$ there are $n>\max(N,4)$, one-qubit unitaries $U_i$ and positive real numbers $k_i$, indexed by $1\le i\le n$, such that, for $|\phi_i\rangle=(U_i^\dagger\otimes I)(|00\rangle+|11\rangle)/\sqrt2$,
--
--   $$ \sum_{i=1}^n k_i|\phi_i\rangle\langle\phi_i|=I_4. $$
--
--   Thus complete qubit Bell POVMs can have arbitrarily many labelled outcomes. Distinct effects or inequivalent protocols are not required, and splitting repeated Bell effects is permitted.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 4, §2 Remark: arbitrarily many qubit teleportation outcomes

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Unboundedly many qubit POVM outcomes, PDF p.4 Remark.
Labels/effects are not required to be distinct: splitting Bell effects is permitted. -/
theorem qubit_teleportation_unbounded_outcomes :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 4 < n ∧
      ∃ (U : Fin n → Matrix Bool Bool ℂ) (k : Fin n → ℝ),
        (∀ i, U i ∈ Matrix.unitaryGroup Bool ℂ) ∧ (∀ i, 0 < k i) ∧ BellFrame U k := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
