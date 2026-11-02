-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_repetitionThreshold
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.repetitionThreshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:41:59.287424+00:00
-- url     : https://prove2.me/theorems/1a2f0ead-62e8-4caa-9327-b9f4208462f3
-- title:
--   III A / Appendix A: exact repetition threshold and Alice/Bob equivalence, (9), (A1)–(A3)
-- statement:
--   Let $n\ge1$, $R_n=\{0^n,1^n\}$, and $0\le Q\le\tfrac12$. Let $P_B(Q)$ be the unnormalized six-state operator after Bob filters on $R_n$, and let $P_{AB}(Q)$ be the operator when both parties filter on that code. Define
--
--   $$F_n(Q)=4Q^{2n}-4Q^n(1-Q)^n+(1-2Q)^{2n}.$$
--
--   Then
--
--   $$\mathrm{Ext}_B(P_B(Q))\Longleftrightarrow
--   \mathrm{Ext}_B(P_{AB}(Q))\Longleftrightarrow F_n(Q)\le0.$$
--
--   The thresholds in the two regimes coincide, and their common value is the least root of $F_n$ in $[0,\tfrac12]$. This specifies the first transition root, because $\tfrac12$ is also a root. The endpoint $Q=\tfrac12$ remains included and is extendable. The result analytically identifies the repetition-code threshold without assuming that Alice's filtering is reversible for general codes.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 10, III A / Appendix A: exact repetition threshold and Alice/Bob equivalence, (9), (A1)–(A3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF pp.4–5, (9), and p.10, (A1)–(A3): exact iff, both filtering regimes,
and the least root (not the extraneous root at 1/2). -/
theorem repetitionThreshold {n : ℕ} (hn : 1 ≤ n) :
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ 1 / 2 →
      (BobExtendible (bobState (repetition (Fin n)) Q) ↔
        BobExtendible (bothState (repetition (Fin n)) Q)) ∧
      (BobExtendible (bothState (repetition (Fin n)) Q) ↔
        repetitionPolynomial n Q ≤ 0)) ∧
    bothThreshold (repetition (Fin n)) = bobThreshold (repetition (Fin n)) ∧
    IsLeast {q : ℝ | 0 ≤ q ∧ q ≤ 1 / 2 ∧ repetitionPolynomial n q = 0}
      (bobThreshold (repetition (Fin n))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
