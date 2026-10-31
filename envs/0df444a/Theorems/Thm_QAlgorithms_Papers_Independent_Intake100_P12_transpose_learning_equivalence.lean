-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_transpose_learning_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.transpose_learning_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:09:25.009094+00:00
-- url     : https://prove2.me/theorems/ace3b0b1-3675-4b66-89c7-15a61d40c378
-- title:
--   Delayed transposition and exact probabilistic learning
-- statement:
--   For $d\ge1$, $k\ge0$ and a real coefficient $p$, the following achievable coefficient conditions are equivalent:
--
--   $$p\in\mathcal A_{\mathrm{delayed\ parallel\ transpose}}(d,k)\quad\Longleftrightarrow\quad p\in\mathcal A_{\mathrm{exact\ unitary\ learning}}(d,k).$$
--
--   In either set $p\in[0,1]$ is independent of the unknown $U\in U(d)$. Learning uses all $k$ oracle slots in a storage process with a one-dimensional input and a finite program memory, before the target input arrives; a fixed two-branch retrieval instrument subsequently implements $X\mapsto pUXU^\dagger$ without new oracle calls. Storage can use the general process model allowed in footnote 14. The transpose side uses a fixed delayed parallel instrument.
--
--   Both directions preserve the constant coefficient; parallelization of learning is used through the source's cited storage/retrieval result.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 15, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.15–16, Lemma 3: both directions between delayed parallel transposition
and exact probabilistic storage/retrieval. The retrieval stage has no oracle calls. -/
theorem transpose_learning_equivalence {d k : ℕ} (hd : 0 < d) (p : ℝ) :
    DelayedAttainable d k (targetChoi .transpose) p ↔ LearningAttainable d k p := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
