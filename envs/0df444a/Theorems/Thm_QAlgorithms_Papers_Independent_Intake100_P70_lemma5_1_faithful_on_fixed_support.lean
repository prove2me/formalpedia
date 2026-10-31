-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_1_faithful_on_fixed_support
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_1_faithful_on_fixed_support
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:42:35.689962+00:00
-- url     : https://prove2.me/theorems/f7ddd2d6-11c0-4634-b7b7-90fea9aa6334
-- title:
--   Lemma 5.1: a positive fixed operator fills the joint fixed support
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Writing $P_0$ for the joint support of all fixed operators, there exists a positive fixed operator $\rho_0$, supported on $P_0$, such that
--
--   $$\mathcal E(\rho_0)=\rho_0,\qquad\ker(\rho_0)\cap P_0=\{0\}.$$
--
--   This gives a faithful operator on the recurrent support, without requiring ambient full rank or trace one.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 22, Lemma 5.1: a positive fixed operator fills the joint fixed support

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

/-- PDF p.22, Lemma 5.1: a positive fixed operator fills P0. It is not assumed
trace one or ambient full rank. The proof uses the Cesaro image of identity. -/
theorem lemma5_1_faithful_on_fixed_support {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E) :
    ∃ rho : Op I, rho.PosSemidef ∧ E rho = rho ∧
      CornerSupported (fixedSupport E) rho ∧ FullRankOn (fixedSupport E) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
