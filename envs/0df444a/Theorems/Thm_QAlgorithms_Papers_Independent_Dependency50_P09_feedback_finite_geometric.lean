-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_feedback_finite_geometric
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.feedback_finite_geometric
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:02:57.91322+00:00
-- url     : https://prove2.me/theorems/eadf544c-ce36-490b-aa19-ee3c0623eba8
-- title:
--   Theorem 22
-- statement:
--   Let $N:A\to B'$ be CPTP, $n\ge1$, $0\le\varepsilon<1$, and $1<\alpha\le2$. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Feedback is free classical communication from Bob to Alice, with an arbitrary finite alphabet in every backward slot; exactly $n$ forward calls are charged. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   C_\leftarrow^{n,\varepsilon}(N)\le\widehat\Upsilon_\alpha(N)+\frac\alpha{n(\alpha-1)}\log_2\frac1{1-\varepsilon}.
--   $$
--
--   This gives the source's operational capacity conclusion in the stated assistance model.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 15, Theorem 22

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

/-- Theorem 22, arXiv:2010.01058v3, PDF pp.15.
 -/
theorem feedback_finite_geometric {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (N : Superop (Fin a) (Fin d)) (hN : IsChannel N)
    (n : ℕ) (hn : 0 < n) (epsilon alpha : ℝ)
    (hepsilon : 0 ≤ epsilon ∧ epsilon < 1)
    (halpha : 1 < alpha ∧ alpha ≤ 2) :
    feedbackFinite N n epsilon ≤ pointUpsilon (geometricD alpha) N +
      (((1 : ℝ)/n : ℝ) : EReal) * penalty alpha epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
