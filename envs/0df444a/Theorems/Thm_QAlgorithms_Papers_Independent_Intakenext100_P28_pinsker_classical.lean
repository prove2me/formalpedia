-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_pinsker_classical
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.pinsker_classical
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:43:31.114839+00:00
-- url     : https://prove2.me/theorems/aa2c0b14-736d-4d90-8b11-bfade9459cfa
-- title:
--   Pinsker inequality (1): separately attributed prior-result interface
-- statement:
--   For probability measures $P,Q$ on any common measurable space and a common logarithm base $b>1$, full L1 total variation satisfies
--
--   $$\frac{|P-Q|^2}{2}\log_b e\le D(P\|Q).$$
--
--   KL is infinite when absolute continuity fails. Sason–Verdu attribute this constant to Csiszar [23], Kullback [60], and independently Kemperman [56], while explaining the folklore Pinsker attribution. The additional logarithmic form $-\ln|P-Q|\ge-\frac12[\ln D_{\rm nats}(P\|Q)+\ln2]$ uses extended logarithms, including zero and infinite endpoints. The original arXiv:1010.1358v5 was independently retrieved: PDF p.3, equations (1),(3),(5)–(6), uses full L1 distance, natural KL and explicitly normalized distributions. Both formulations are represented; this is a draft interface awaiting mechanical and independent review, not an already accepted reuse.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 2, Pinsker inequality (1)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Pinsker inequality (1): separately attributed prior-result interface. Sason--Verdu, arXiv:1508.00335v7, PDF p.2.  -/
theorem pinsker_classical
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    fullVariation P Q ^ 2 / 2 * ENNReal.ofReal (logBaseE b) ≤ kl b P Q ∧
    -ENNReal.log (fullVariation P Q) ≥ -((1 / 2 : ℝ) : EReal) *
      (ENNReal.log (InformationTheory.klDiv P Q) + (Real.log 2 : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
