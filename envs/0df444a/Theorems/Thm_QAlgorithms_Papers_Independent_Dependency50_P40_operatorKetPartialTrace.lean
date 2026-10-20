-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_operatorKetPartialTrace
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.operatorKetPartialTrace
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:18:51.074808+00:00
-- url     : https://prove2.me/theorems/a14f68a1-b2e1-4af8-bbaf-f5bceec94261
-- title:
--   Partial trace of an operator-ket dyad
-- statement:
--   Let $H_1=\mathbb C^k$ and $H_2=\mathbb C^h$, with $h,k>0$, and let $C_1,C_2:H_2\to H_1$ be arbitrary matrices. Use the unnormalized operator kets with output factor first. Then
--
--   $$
--   \operatorname{tr}_{H_2}(|C_1\rangle\rangle\langle\langle C_2|)=C_1C_2^\dagger.
--   $$
--
--   The dyad conjugates the second vector, and the partial trace preserves off-diagonal output entries. This identity is the algebraic basis for channel reconstruction.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 3, III, Eq. (12): partial trace of a dyad of operator kets

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.3, (12): tracing out the input factor of an operator-ket dyad. -/
theorem operatorKetPartialTrace {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (C1 C2 : Matrix (Fin k) (Fin h) ℂ) :
    traceRight (dyad (operatorKet C1) (operatorKet C2)) = C1 * C2ᴴ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
