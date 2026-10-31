-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_8_adjoint_extension
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_8_adjoint_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:47:43.909354+00:00
-- url     : https://prove2.me/theorems/f5cac63d-081a-4083-b0cb-e521a576b91f
-- title:
--   Lemma 5.8: every A element extends to an adjoint fixed point
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $P_0$ be the fixed support and $A=\operatorname{Fix}(\mathcal E_0^\dagger)$. For every $X_0\in A$,
--
--   $$\exists X\in B(H),\quad\mathcal E^\dagger(X)=X,\qquad P_0XP_0=X_0.$$
--
--   No resolvent invertibility hypothesis is added. This lemma states existence; Theorem 5 also states uniqueness.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 24, Lemma 5.8: every A element extends to an adjoint fixed point

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

/-- PDF pp.24–25, Lemma 5.8: every computed corner-algebra element extends.
Invertibility of the transient resolvent is derived, not an extra assumption. -/
theorem lemma5_8_adjoint_extension {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (X0 : Op I) (hX : X0 ∈ cornerAlgebra E) :
    ∃ X : Op I, channelAdjoint E X = X ∧ fixedSupport E * X * fixedSupport E = X0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
