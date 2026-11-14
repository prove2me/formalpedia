-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_rotatedEntangledKet_inner
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.rotatedEntangledKet_inner
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T03:51:28.936871+00:00
-- url     : https://prove2.me/theorems/c7550eee-791b-4fc6-9bf0-86698b6b9b63
-- title:
--   Bell-ket overlaps equal normalized Hilbert–Schmidt products
-- statement:
--   Let $I$ be a nonempty finite basis with $d=|I|$, let $U,V$ be arbitrary complex $d\times d$ matrices, and write $|\Phi\rangle=d^{-1/2}\sum_i|i,i\rangle$ and $|\Phi_U\rangle=(U^\dagger\otimes I)|\Phi\rangle$. Then
--
--   $$\langle\Phi_U\mid\Phi_V\rangle=\frac{\operatorname{Tr}(UV^\dagger)}{d}.$$
--
--   No unitarity assumption is needed. This overlap identity supplies the exact normalization in the operator-basis criterion for teleportation and transfers Hilbert–Schmidt orthogonality to Bell measurements.
-- source:
--   R. Jozsa, An introduction to measurement based quantum computation, https://arxiv.org/abs/quant-ph/0508124v2, PDF p.4, Remark following Lemma 2; expanded overlap identity underlying the corrected trace criterion.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P21 QAlgorithms.Papers.Independent.Intakenext100.P52

theorem QAlgorithms.Papers.Independent.Intakenext100.P52.rotatedEntangledKet_inner {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U V : Matrix I I ℂ) :
    inner ℂ (rotatedEntangledKet U) (rotatedEntangledKet V) =
      (Fintype.card I : ℂ)⁻¹ * (U * Vᴴ).trace := by sorry
