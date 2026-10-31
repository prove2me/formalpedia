-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_samson_constants_sharp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.samson_constants_sharp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:43:54.976341+00:00
-- url     : https://prove2.me/theorems/0b47f9d5-d2a3-4111-a5bc-5210f8f6a31b
-- title:
--   Optimality of Samson and one-sided Marton constants (129),(136)
-- statement:
--   Over all distinct mutually absolutely continuous probability pairs on arbitrary alphabets, the least universal coefficient for each comparison
--
--   $$d_2^2(P,Q)+d_2^2(Q,P)\le C D(P\|Q),\qquad
--   d_2^2(P,Q)\le C\min\{D(P\|Q),D(Q\|P)\}$$
--
--   is $C=2/(\log_b e)$. This records the new optimality assertions (129) and Remark 7, without assigning original authorship of Samson's inequality to this paper.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 20, Optimality of Samson and one-sided Marton constants (129),(136)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Optimality of Samson and one-sided Marton constants (129),(136). Sason--Verdu, arXiv:1508.00335v7, PDF p.20.  -/
theorem samson_constants_sharp
    (b : LogBase) :
    Sharp martonSum (kl b) mutualPairs (ENNReal.ofReal (2 / logBaseE b)) ∧
    Sharp marton (fun P Q => min (kl b P Q) (kl b Q P)) mutualPairs
      (ENNReal.ofReal (2 / logBaseE b)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
