-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_5_distortion_exhausts_fixed
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_5_distortion_exhausts_fixed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:45:34.454875+00:00
-- url     : https://prove2.me/theorems/a9f0c8ec-497f-4fac-8e3e-68283d74ca7a
-- title:
--   Lemma 5.5: the constructed distorted algebra exhausts fixed points
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Fix canonical coordinates for the computed corner algebra, and the positive factors $\tau_k$ of trace $\dim B_k$ constructed as in Lemma 5.4, so that $\widetilde A=\bigoplus_kM_{A_k}\otimes\tau_k$ consists of fixed operators. Then
--
--   $$\operatorname{Fix}(\mathcal E)\subseteq\widetilde A.$$
--
--   Together with the previous inclusion, this exhausts the fixed operators. No equality or arbitrary unrelated distorted set is assumed.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 23, Lemma 5.5: the constructed distorted algebra exhausts fixed points

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

/-- PDF pp.23–24, Lemma 5.5. These are the same normalized factors constructed
in Lemma 5.4, characterized by positivity, trace and the previously established
inclusion; equality is not a premise. -/
theorem lemma5_5_distortion_exhausts_fixed {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (B : BlockModel I) (hB : IsFixedDecomposition E B)
    (tau : (k : Fin B.sectors) → Op (Fin (B.gaugeDim k)))
    (hTau : B.DistortionFactors tau) (hFixed : B.blockSpace tau ⊆ fixedOperators E) :
    fixedOperators E ⊆ B.blockSpace tau := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
