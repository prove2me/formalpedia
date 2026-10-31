-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_unrestrictedTwoSidedInversion
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.unrestrictedTwoSidedInversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:59:36.668111+00:00
-- url     : https://prove2.me/theorems/eae0786a-bcf1-4ef9-832f-ce8d40abdc2a
-- title:
--   Constructive unrestricted two-sided inversion
-- statement:
--   Let $n\ge1$ and let $U\in\mathrm{SU}(2^n)$. Set $U_1=U^{-1}U^{-1}$ and $U_2=I$, both in the same special-unitary group. Then
--
--   $$U_1 U U_2=U^{-1}.$$
--
--   This supplies an unrestricted two-sided inverse for every special-unitary matrix. It makes no universal claim that the analogous task with local factors is impossible.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 13, Remark 2: unrestricted two-sided inversion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Remark 2, PDF p.13: a constructive unrestricted two-sided SU(N)
inversion. No local impossibility assertion is extracted from the remark. -/
theorem unrestrictedTwoSidedInversion {n : ℕ} (hn : 0 < n)
    (U : Matrix.specialUnitaryGroup (QAlgorithms.Qubits n) ℂ) :
    (U⁻¹ * U⁻¹) * U * 1 = U⁻¹ ∧
    ∃ U1 U2 : Matrix.specialUnitaryGroup (QAlgorithms.Qubits n) ℂ,
      U1 * U * U2 = U⁻¹ := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
