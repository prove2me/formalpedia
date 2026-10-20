-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_feedback_strongConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.feedback_strongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:03:51.845605+00:00
-- url     : https://prove2.me/theorems/39ab5342-622b-4b04-a85e-7accdb951ea7
-- title:
--   Theorem 23
-- statement:
--   Let $N:A\to B'$ be CPTP, with free arbitrary finite classical feedback alphabets. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   \widetilde C_\leftarrow(N)\le\widehat\Upsilon(N),\qquad C_\leftarrow(N)\le\widehat\Upsilon(N)\le C_\beta(N).
--   $$
--
--   This gives the source's operational capacity conclusion in the stated assistance model.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 16, Theorem 23

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

/-- Theorem 23, arXiv:2010.01058v3, PDF pp.16.
 -/
theorem feedback_strongConverse {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (N : Superop (Fin a) (Fin d)) (hN : IsChannel N) :
    feedbackStrong N ≤ pointUpsilon bsD N ∧
      feedbackCapacity N ≤ pointUpsilon bsD N ∧ pointUpsilon bsD N ≤ cBeta (pointMap N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
