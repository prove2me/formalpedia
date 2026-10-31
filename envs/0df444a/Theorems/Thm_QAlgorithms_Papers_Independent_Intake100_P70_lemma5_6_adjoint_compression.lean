-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_6_adjoint_compression
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_6_adjoint_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:46:22.852614+00:00
-- url     : https://prove2.me/theorems/0d50d346-5e72-4a5c-a4ee-84d4434d9b9e
-- title:
--   Lemma 5.6: compression of adjoint fixed points lies in A
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $P_0$ be the joint fixed support and $A=\operatorname{Fix}(\mathcal E_0^\dagger)$ the computed corner algebra. Then
--
--   $$\mathcal E^\dagger(X)=X\quad\Longrightarrow\quad P_0XP_0\in A.$$
--
--   This is two-sided compression; existence of every extension is a separate assertion.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 24, Lemma 5.6: compression of adjoint fixed points lies in A

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.24, Lemma 5.6: two-sided compression of full adjoint fixed points. -/
theorem lemma5_6_adjoint_compression {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (X : Op I) (hX : channelAdjoint E X = X) :
    fixedSupport E * X * fixedSupport E ∈ cornerAlgebra E := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
