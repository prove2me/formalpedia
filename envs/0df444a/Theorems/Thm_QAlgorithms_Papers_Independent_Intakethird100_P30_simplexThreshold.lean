-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_simplexThreshold
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.simplexThreshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:47:01.92844+00:00
-- url     : https://prove2.me/theorems/f56d6ae7-3343-4ed0-a96b-3eb8715bf47c
-- title:
--   IV A: simplex codes do not exceed repetition thresholds
-- statement:
--   Let $C$ be an equidistant binary code of $m\ge2$ distinct words of length $n\ge1$, with no constant columns, and common distance $1\le d\le n$. Let $Q_{C,\mathrm{both}}^*$ be the symmetric-extendability threshold when Alice and Bob both postselect on this same code, and let $Q_{R_n}^*$ be the repetition-code threshold. Then
--
--   $$Q_{C,\mathrm{both}}^*\le Q_{R_n}^*\le c,
--   \qquad c=\frac{5-\sqrt5}{10}.$$
--
--   For every $Q\in[c,\tfrac12]$, the constructed both-party filtered operator is symmetrically extendable. Thus same-code simplex postselection cannot break symmetric extendability in the gap above Chau's threshold. This is specifically the both-party regime; no Bob-only simplex threshold equivalence is assumed.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 8, IV A: simplex codes do not exceed repetition thresholds

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.8: simplex thresholds in the BOTH-party regime do not exceed the
same-length repetition threshold or Chau's limit. No Bob-only simplex claim. -/
theorem simplexThreshold {n m d : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hd0 : 1 ≤ d) (hdn : d ≤ n) (C : Fin m → Qubits n)
    (hC : Function.Injective C) (hd : Equidistant C d) (hcols : NoConstantColumns C) :
    bothThreshold C ≤ bobThreshold (repetition (Fin n)) ∧
    bobThreshold (repetition (Fin n)) ≤ chau ∧
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / 2 → chau ≤ Q → BobExtendible (bothState C Q)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
