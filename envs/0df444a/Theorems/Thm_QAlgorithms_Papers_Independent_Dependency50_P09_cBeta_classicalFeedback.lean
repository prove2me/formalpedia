-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_cBeta_classicalFeedback
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_classicalFeedback
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:50:55.141006+00:00
-- url     : https://prove2.me/theorems/86dde0b4-a310-4189-b974-0e3756645f4d
-- title:
--   Proposition 4 (Zero on classical feedback channels)
-- statement:
--   Let $d\ge1$. The classical feedback channel $\Delta:B\to A'$ completely dephases in the fixed computational basis and relabels Bob's $d$-dimensional input as Alice's output; Alice's input and Bob's output are trivial.
--
--   $$
--   C_\beta(\Delta)=0,\qquad \Delta(X)=\sum_{i=0}^{d-1}\langle i|X|i\rangle |i\rangle\langle i|.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 6, Proposition 4 (Zero on classical feedback channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 4 (Zero on classical feedback channels), arXiv:2010.01058v3, PDF pp.6.
 -/
theorem cBeta_classicalFeedback {d : ℕ} (hd : 0 < d) :
    cBeta (feedbackMap d) = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
