-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_4_distorted_fixed_subspace
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_4_distorted_fixed_subspace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:44:49.431281+00:00
-- url     : https://prove2.me/theorems/f8c92c16-064b-4369-9130-39ceffe5cdc5
-- title:
--   Lemma 5.4: a distorted algebra of fixed operators exists
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. For any canonical coordinates $A=\operatorname{Fix}(\mathcal E_0^\dagger)=\bigoplus_kM_{A_k}\otimes I_{B_k}$ on the fixed support, there exist positive matrices $\tau_k$ on $B_k$ with $\operatorname{Tr}\tau_k=\dim B_k$ such that
--
--   $$\widetilde A=\bigoplus_kM_{A_k}\otimes\tau_k\subseteq\operatorname{Fix}(\mathcal E).$$
--
--   The trace normalization makes this a genuine trace-preserving distortion and prevents an all-zero witness.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 23, Lemma 5.4: a distorted algebra of fixed operators exists

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

/-- PDF p.23, Lemma 5.4: a genuine normalized distortion consists of fixed
operators. Nonzero gauge factors are forced by their positive traces. -/
theorem lemma5_4_distorted_fixed_subspace {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (B : BlockModel I) (hB : IsFixedDecomposition E B) :
    ∃ tau : (k : Fin B.sectors) → Op (Fin (B.gaugeDim k)),
      B.DistortionFactors tau ∧ B.blockSpace tau ⊆ fixedOperators E := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
