-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_trace_norm_hilbert_schmidt
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.trace_norm_hilbert_schmidt
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:57:05.569482+00:00
-- url     : https://prove2.me/theorems/76619624-97fc-4b30-bf19-1af41562a62b
-- title:
--   Lemma 13: trace norm versus Hilbert–Schmidt norm
-- statement:
--   For every operator $X$ on a finite complex space, let $d=\operatorname{rank}X$, the dimension of the support of $|X|=\sqrt{X^\dagger X}$. Then
--   $$\|X\|_1^2\le d\|X\|_2^2.$$
--   The norms are the trace and Hilbert–Schmidt norms. No positivity, normalization, or Hermiticity is assumed, and the zero operator and zero-dimensional ambient space are included. This is the singular-value norm comparison used in decoupling.
--
--   **Formalization Note** The source's nonzero-eigenvalue support gloss is corrected to singular support; it would otherwise fail for a nonzero nilpotent.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 20, Lemma 13: trace norm versus Hilbert–Schmidt norm

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.20, Lemma 13, (A1): arbitrary finite complex operator.
Printed: support described by nonzero eigenvalues. Changed: rank(X), the
support dimension of |X|. Why: the proof uses singular values and the
printed gloss fails for nonzero nilpotents. No Hermiticity is added. -/
theorem trace_norm_hilbert_schmidt {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) :
    traceNorm X ^ 2 ≤ (Matrix.rank X : ℝ) * frobNorm X ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
