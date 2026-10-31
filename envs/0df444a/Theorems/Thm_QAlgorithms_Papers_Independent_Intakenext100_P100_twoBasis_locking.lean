-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_twoBasis_locking
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.twoBasis_locking
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:16:41.439651+00:00
-- url     : https://prove2.me/theorems/1e0f7601-0fdb-4cfe-b123-bcf375ca5e10
-- title:
--   Separable two-basis one-bit locking
-- statement:
--   Let $d\ge1$. Let $U_0=I$ and $U_1$ be unitary on $\mathbb C^d$, with the computational basis and the columns of $U_1$ mutually unbiased. For independent uniform $k\in\{0,\ldots,d-1\}$ and $t\in\{0,1\}$, define
--   $$\rho=\frac1{2d}\sum_{k,t}|k,t\rangle\langle k,t|_A\otimes U_t|k\rangle\langle k|U_t^\dagger{}_B.$$
--   This is a separable density state. Write $I_c$ for the supremum of Shannon mutual information in bits over all independent finite local POVMs, and $I_c^{(1)}$ for its optimum after at most one Alice-to-Bob classical bit. Disclosing $t$, undoing $U_t$ and measuring $k$ leaves both parties with $(k,t)$, in the normalized classical state $\rho'$. Then
--   $$I_c(\rho)=\tfrac12\log_2 d,\qquad I_c(\rho')=I_c^{(1)}(\rho)=1+\log_2 d,\qquad I_c^{(1)}(\rho)-I_c(\rho)=1+\tfrac12\log_2 d.$$
--   This is the paper's explicit separable locking example, with the disclosed key counted in the final correlation.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 2, Eq. (5), conclusion on PDF p. 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3, Eq.(5): separable two-basis locking, including the retained
key bit and the optimized one-way one-bit value. The final state is the
explicit decoded disclosure output, not an unrelated state variable. -/
theorem twoBasis_locking (d : ℕ) (hd : 0 < d)
    (U : Fin 2 → Matrix.unitaryGroup (Fin d) ℂ) (hU : IsUnbiasedFamily U) :
    IsDensityMatrix (lockingState U) ∧
    Entanglement.IsSeparablePositive (lockingState U) ∧
    IsDensityMatrix (disclosedState d 2) ∧
    (∃ P : OneWayMap (Fin d × Fin 2) (Fin d) (Fin d × Fin 2) (Fin d × Fin 2) 1,
      P.messages = 2 ∧ oneWayOutput P (lockingState U) = disclosedState d 2) ∧
    lockingMeasuredInformation (lockingState U) = (1 / 2 : ℝ) * Real.logb 2 d ∧
    lockingMeasuredInformation (disclosedState d 2) = 1 + Real.logb 2 d ∧
    oneWayInformation 1 (lockingState U) = 1 + Real.logb 2 d ∧
    oneWayInformation 1 (lockingState U) - lockingMeasuredInformation (lockingState U) =
      1 + (1 / 2 : ℝ) * Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
