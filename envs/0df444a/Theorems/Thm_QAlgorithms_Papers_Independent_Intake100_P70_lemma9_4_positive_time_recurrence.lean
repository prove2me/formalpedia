-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma9_4_positive_time_recurrence
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma9_4_positive_time_recurrence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:49:42.669694+00:00
-- url     : https://prove2.me/theorems/59725e34-be8b-4757-b05f-8f1f51de24bf
-- title:
--   Lemma 9.4: simultaneous positive-time recurrence on rotating points
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $\mathcal E_R$ be its restriction to the complex rotating space, with the norm induced by the Hilbert–Schmidt vector norm. For every real $\varepsilon>0$,
--
--   $$\exists N\ge1,\qquad\|\mathcal E_R^N-I_R\|_{2\to2}<\varepsilon.$$
--
--   A single bound applies uniformly to every rotating operator. The time is strictly positive, without a normality or orthonormal-eigenbasis premise.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 27, Lemma 9.4: simultaneous positive-time recurrence on rotating points

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

/-- PDF pp.27–28, Lemma 9.4: simultaneous positive-time recurrence in the
induced Hilbert–Schmidt norm. N=0 is excluded, as in the proof's N=s-r>0.
No orthonormal peripheral eigenbasis or rational-phase shortcut is assumed. -/
theorem lemma9_4_positive_time_recurrence {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, 0 < N ∧ RotatingRecurrence E N eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
