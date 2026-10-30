-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_cerf_qubit
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.cerf_qubit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:07:25.751255+00:00
-- url     : https://prove2.me/theorems/4957e334-540b-4fac-ad26-3c0a342d1d45
-- title:
--   §II.C.2 Eqs.(30)–(31): equivalent qubit Cerf representation
-- statement:
--   For real signed parameters $v,x$ with $v^2+3x^2=1$, the ambient operator $V=vI+x\sum_k\sigma_k\otimes\sigma_k\otimes I$ acts on the specified input subspace as
--
--   $$
--   V(|\psi\rangle_A\Phi^+_{BM})=(v-x)|\psi\rangle_A\Phi^+_{BM}+2x|\psi\rangle_B\Phi^+_{AM}.
--   $$
--
--   There exists a single full unitary with exactly this action for all input vectors. No unitarity of the displayed ambient V is asserted.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 11, §II.C.2 Eqs.(30)–(31): equivalent qubit Cerf representation

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

/-- II.C.2, PDF p.11 Eqs.(30)–(31): signed parameters are allowed; only the
specified input subspace is isometric. No assertion that the ambient Cerf operator is unitary. -/
theorem cerf_qubit (v x : ℝ) (h : v ^ 2 + 3 * x ^ 2 = 1) :
    ∃ U : Matrix.unitaryGroup (Triple 2) ℂ, ∀ psi : EuclideanSpace ℂ (Fin 2),
      WithLp.toLp 2 ((U : Matrix (Triple 2) (Triple 2) ℂ).mulVec (tensorVec psi (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin 2)))) =
        asymmetricOutput (v - x) (2 * x) psi ∧
      WithLp.toLp 2 ((cerfQubit v x).mulVec (tensorVec psi (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin 2)))) =
        asymmetricOutput (v - x) (2 * x) psi := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
