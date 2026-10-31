-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_7_transient_has_no_nonzero_fixed
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_7_transient_has_no_nonzero_fixed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:47:05.981096+00:00
-- url     : https://prove2.me/theorems/654810ec-d917-4fe5-a637-6c8b41c98298
-- title:
--   Lemma 5.7: the transient operator-space block has no eigenvalue 1
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $P_0$ be the joint fixed support. Identify the Hilbert–Schmidt complement of $B(P_0)$ with $\{X:P_0XP_0=0\}$ and define $L_F(X)=\mathcal E(X)-P_0\mathcal E(X)P_0$. Then
--
--   $$P_0XP_0=0,\quad L_F(X)=X\quad\Longrightarrow\quad X=0.$$
--
--   The complement includes physical off-diagonal blocks. The source phrase “no fixed points” excludes only nonzero fixed vectors.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 24, Lemma 5.7: the transient operator-space block has no eigenvalue 1

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

/-- PDF p.24, Lemma 5.7. Printed 'no fixed points' means no NONZERO fixed
vectors. P0 X P0=0 describes the whole Hilbert–Schmidt corner complement,
including off-diagonal physical blocks, and LF(X)=E(X)-P0 E(X)P0. -/
theorem lemma5_7_transient_has_no_nonzero_fixed {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (X : Op I) (hCorner : fixedSupport E * X * fixedSupport E = 0)
    (hFixed : E X - fixedSupport E * E X * fixedSupport E = X) : X = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
