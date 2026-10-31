-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_operator_basis_trace_criterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.operator_basis_trace_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:35:15.753242+00:00
-- url     : https://prove2.me/theorems/9d6a9985-c4d1-4366-a2a3-e018d9831546
-- title:
--   §2 Remark: orthogonal unitary bases and entangled bases
-- statement:
--   Let $I$ be a nonempty finite basis with $d$ elements and let $U_1,\ldots,U_{d^2}$ be unitary matrices on it. For normalized $|\phi\rangle=d^{-1/2}\sum_i|i,i\rangle$, set $|\phi(U_a)\rangle=(U_a^\dagger\otimes I)|\phi\rangle$. Then
--
--   $$ \{|\phi(U_a)\rangle\}_a\text{ is orthonormal}\quad\Longleftrightarrow\quad \operatorname{Tr}(U_aU_b^\dagger)=d\,\delta_{ab}\quad\text{for all }a,b. $$
--
--   This identifies orthogonal unitary operator bases with maximally entangled measurement bases. **Source correction:** the printed formula omits $d$ on the right; ordinary trace has $\operatorname{Tr}(I_d)=d$.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 4, §2 Remark: orthogonal unitary bases and entangled bases

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Orthogonal operator bases, PDF p.4 Remark, corrected source typo:
printed Tr(U_i U_j†)=delta_ij; changed to d delta_ij because phi is normalized
and the ordinary unnormalized trace has Tr(I_d)=d. -/
theorem operator_basis_trace_criterion {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U : Fin (Fintype.card I ^ 2) → Matrix I I ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup I ℂ) :
    Orthonormal ℂ (fun i => rotatedEntangledKet (U i)) ↔
      ∀ i j, (U i * (U j)ᴴ).trace = if i = j then (Fintype.card I : ℂ) else 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
