-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_trace_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P02.trace_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:31:40.123653+00:00
-- url     : https://prove2.me/theorems/3d45c4e5-e2d2-4744-a981-b820130964bb
-- title:
--   Convergent basis traces, cyclicity and bounded linearity
-- statement:
--   Let $H$ be a complete real or complex Hilbert space and define the trace of a trace-class $T$ by the actual convergent sum $\operatorname{tr}(T)=\sum_i\langle Te_i;e_i\rangle$. For every complete orthonormal basis the diagonal is absolutely summable and
--
--   $$
--   \sum_i|\langle Te_i;e_i\rangle|\le\|T\|_1,
--   $$
--
--   and its sum equals the same trace. For every bounded endomorphism $S$, all product-diagonal sums below converge and
--
--   $$
--   |\operatorname{tr}(T)|\le\|T\|_1,\qquad
--   \operatorname{tr}(T^*)=\overline{\operatorname{tr}(T)},\qquad
--   \operatorname{tr}(TS)=\operatorname{tr}(ST),
--   $$
--   $$
--   |\operatorname{tr}(S|T|)|=|\operatorname{tr}(|T|S)|\le\|S\|\,\|T\|_1,
--   \qquad \operatorname{tr}(|T|)=\|T\|_1.
--   $$
--
--   The trace is additive and scalar linear on trace class, and the first bound makes it a bounded linear functional in trace norm. These statements preserve both the basis-sum construction and all of Claim 3.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 12, §5, Claim 3 and unnumbered trace properties

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.12–13,16, Claim 3 and trace properties: actual basis sums, convergence,
linearity, boundedness, adjoint conjugation, cyclicity, and the modulus-trace norm.
The first-linear source inner is transcribed by reversing Lean inner arguments. -/
theorem trace_properties :
    (∀ {I : Type*} (b : HilbertBasis I F H) (T : H →L[F] H), IsModulusTraceClass T →
      Summable (fun i => ‖basisDiagonal b T i‖) ∧
      (∑' i, ‖basisDiagonal b T i‖) ≤ modulusTraceNorm T ∧ HasSum (basisDiagonal b T) (basisOperatorTrace T) ∧
      HasSum (basisDiagonal b (hilbertOperatorModulus T)) (modulusTraceNorm T : F)) ∧
    (∀ T : H →L[F] H, IsModulusTraceClass T →
      ‖basisOperatorTrace T‖ ≤ modulusTraceNorm T ∧
      basisOperatorTrace (ContinuousLinearMap.adjoint T) = star (basisOperatorTrace T) ∧
      basisOperatorTrace (hilbertOperatorModulus T) = (modulusTraceNorm T : F)) ∧
    (∀ {I : Type*} (b : HilbertBasis I F H) (T S : H →L[F] H), IsModulusTraceClass T →
      HasSum (basisDiagonal b (T.comp S)) (basisOperatorTrace (T.comp S)) ∧
      HasSum (basisDiagonal b (S.comp T)) (basisOperatorTrace (S.comp T)) ∧
      HasSum (basisDiagonal b (S.comp (hilbertOperatorModulus T))) (basisOperatorTrace (S.comp (hilbertOperatorModulus T))) ∧
      HasSum (basisDiagonal b ((hilbertOperatorModulus T).comp S)) (basisOperatorTrace ((hilbertOperatorModulus T).comp S)) ∧
      basisOperatorTrace (T.comp S) = basisOperatorTrace (S.comp T) ∧
      ‖basisOperatorTrace (S.comp (hilbertOperatorModulus T))‖ = ‖basisOperatorTrace ((hilbertOperatorModulus T).comp S)‖ ∧
      ‖basisOperatorTrace ((hilbertOperatorModulus T).comp S)‖ ≤ ‖S‖ * modulusTraceNorm T) ∧
    (∀ T U : H →L[F] H, IsModulusTraceClass T → IsModulusTraceClass U →
      basisOperatorTrace (T + U) = basisOperatorTrace T + basisOperatorTrace U) ∧
    (∀ (a : F) (T : H →L[F] H), IsModulusTraceClass T → basisOperatorTrace (a • T) = a * basisOperatorTrace T) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
