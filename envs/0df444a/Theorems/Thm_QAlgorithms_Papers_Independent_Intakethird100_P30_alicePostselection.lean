-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_alicePostselection
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.alicePostselection
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:45:43.8046+00:00
-- url     : https://prove2.me/theorems/ba1beb0c-cb7a-405a-9096-3820f8c4851c
-- title:
--   IV: Alice filtering cannot increase the threshold, (20)
-- statement:
--   Let $C=(C_k)_{k\in K}$ be any nonempty code of distinct $n$-bit words, $n\ge1$, and define $K_C=\sum_k|k\rangle\langle C_k|$. For $0\le Q\le\tfrac12$, let $P_B(Q)$ and $P_{AB}(Q)$ be the six-state operators after Bob-only and same-code Alice/Bob filtering. The latter is positive with strictly positive trace and satisfies
--
--   $$P_{AB}(Q)=(K_C\otimes I)P_B(Q)(K_C\otimes I)^\dagger,$$
--
--   so
--
--   $$\mathrm{Ext}_B(P_B(Q))\Longrightarrow\mathrm{Ext}_B(P_{AB}(Q)),
--   \qquad Q_{C,\mathrm{both}}^*\le Q_{C,\mathrm{Bob}}^*.$$
--
--   All filtered operators are unnormalized. This shows that allowing this extra Alice filter cannot increase the threshold. The converse is not asserted for arbitrary codes; the repetition-code equivalence is stated separately.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 7, IV: Alice filtering cannot increase the threshold, (20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.7, (20): actual Alice-filter factorization and preservation of extendability,
with the threshold comparison in the correct direction. -/
theorem alicePostselection {n : ℕ} (hn : 1 ≤ n) [Nonempty K]
    (C : K → Qubits n) (hC : Function.Injective C) :
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / 2 →
      (bothState C Q).PosSemidef ∧ 0 < (bothState C Q).trace.re ∧
      bothState C Q =
        Matrix.kronecker (codeKraus C) (1 : Matrix K K ℂ) * bobState C Q *
          (Matrix.kronecker (codeKraus C) (1 : Matrix K K ℂ))ᴴ ∧
      (BobExtendible (bobState C Q) → BobExtendible (bothState C Q))) ∧
    bothThreshold C ≤ bobThreshold C := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
