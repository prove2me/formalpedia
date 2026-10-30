-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_cerf_qudit
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.cerf_qudit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:08:08.471794+00:00
-- url     : https://prove2.me/theorems/a1a44a09-21d6-4eca-b9a0-4f1860a245db
-- title:
--   §II.C.2 Eqs.(32)–(33): corrected general-d Cerf representation
-- statement:
--   Let $d\ge2$, $v,x\in\mathbb R$, $v^2+(d^2-1)x^2=1$, and $U_{mn}|k\rangle=e^{2\pi i kn/d}|k+m\rangle$. Correct the second factor of the printed (32) to its adjoint. Then
--
--   $$
--   \left[vI+x\!\sum_{(m,n)\ne(0,0)}U_{mn}\otimes U_{mn}^{\dagger}\otimes I\right]|\psi\rangle_A\Phi_{BM}=(v-x)|\psi\rangle_A\Phi_{BM}+dx|\psi\rangle_B\Phi_{AM}.
--   $$
--
--   This subspace action has a full unitary extension. The corrected formula follows the source’s distributor output and specializes to its Pauli representation; independent moderation of the correction remains required.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 11, §II.C.2 Eqs.(32)–(33): corrected general-d Cerf representation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.C.2, PDF p.11 Eqs.(32)–(33): corrected adjoint and transpose conventions.
Printed U_mn tensor U_mn is changed to U_mn tensor U_mn† by the swap identity;
(A tensor I)Phi=(I tensor A^T)Phi, not the printed conjugation rule. -/
theorem cerf_qudit (d : ℕ) (hd : 2 ≤ d) (v x : ℝ)
    (h : v ^ 2 + ((d : ℝ) ^ 2 - 1) * x ^ 2 = 1) :
    ∃ U : Matrix.unitaryGroup (Triple d) ℂ, ∀ psi : EuclideanSpace ℂ (Fin d),
      WithLp.toLp 2 ((U : Matrix (Triple d) (Triple d) ℂ).mulVec (tensorVec psi (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin d)))) =
        asymmetricOutput (v - x) (d * x) psi ∧
      WithLp.toLp 2 ((cerfQudit d v x).mulVec (tensorVec psi (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin d)))) =
        asymmetricOutput (v - x) (d * x) psi := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
