-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_feedback_strong_covariant
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.feedback_strong_covariant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:08:33.257288+00:00
-- url     : https://prove2.me/theorems/647837c9-04ed-4432-b820-d743294cb0c0
-- title:
--   Corollary 31
-- statement:
--   Let $N$ be a point-to-point channel covariant under an input unitary one-design and a matching output unitary representation. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Free classical feedback is allowed; $\Upsilon$ uses Umegaki relative entropy. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   \widetilde C_\leftarrow(N)\le\Upsilon(N).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** The feedback arrow in (334) and the surrounding construction determine the assisted capacity despite its omission from the prose sentence.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 19, Corollary 31

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

/-- Corollary 31, arXiv:2010.01058v3, PDF pp.19.
The feedback arrow in (334) and the surrounding construction determine the assisted capacity despite its omission from the prose sentence.
Source correction: Printed: The prose omits classical-feedback assistance. Changed: Use the feedback-assisted strong-converse capacity. Why: Equation (334) contains the feedback arrow and follows the feedback-assisted Corollary 30. -/
theorem feedback_strong_covariant {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (N : Superop (Fin a) (Fin d)) (hN : IsChannel N)
    (hcov : HasPointDesign N) :
    feedbackStrong N ≤ pointUpsilon relativeD N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
