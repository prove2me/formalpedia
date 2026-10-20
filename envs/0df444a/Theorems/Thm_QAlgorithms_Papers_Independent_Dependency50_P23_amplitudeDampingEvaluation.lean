-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_amplitudeDampingEvaluation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.amplitudeDampingEvaluation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:43:26.671061+00:00
-- url     : https://prove2.me/theorems/4445390e-5015-49ac-a5b8-ea1f15668290
-- title:
--   Theorem 14: amplitude-damping β and ζ evaluation
-- statement:
--   For $0\le\gamma\le1$, let $\mathcal N_\gamma^{\mathrm{AD}}(X)=E_0XE_0^\dagger+E_1XE_1^\dagger$, where $E_0=|0\rangle\langle0|+\sqrt{1-\gamma}|1\rangle\langle1|$ and $E_1=\sqrt\gamma|0\rangle\langle1|$. Then
--
--   $$C_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N_\gamma^{\mathrm{AD}})\le C_\zeta(\mathcal N_\gamma^{\mathrm{AD}})=C_\beta(\mathcal N_\gamma^{\mathrm{AD}})=\log_2(1+\sqrt{1-\gamma}),$$
--
--   $$C(\mathcal N_\gamma^{\mathrm{AD}})\le\log_2(1+\sqrt{1-\gamma}).$$
--
--   Both endpoint channels are included. This evaluates the two strong-converse SDPs exactly on the amplitude-damping family.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 17, Theorem 14

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF pp.17–18, Theorem 14: exact Kraus-form amplitude damping on 0≤gamma≤1. -/
theorem amplitudeDampingEvaluation (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    nsCapacity true (AD gamma) ≤ cZeta (AD gamma) ∧
    cZeta (AD gamma) = cBeta (AD gamma) ∧
    cBeta (AD gamma) = log2 (1 + Real.sqrt (1 - gamma)) ∧
    ordinaryClassicalCapacity (AD gamma) ≤ log2 (1 + Real.sqrt (1 - gamma)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
