-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_nonidentical_finiteCode
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.nonidentical_finiteCode
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:15:37.001077+00:00
-- url     : https://prove2.me/theorems/30917a57-fb9b-436a-8ab6-74edb5ee0a00
-- title:
--   Unnumbered nonidentical-channel finite-code bound (281)
-- statement:
--   Let a fixed legal $(n,M,\varepsilon)$ maximum-error forward code use possibly distinct bipartite channels $N^{(1)},\ldots,N^{(n)}$, with $n,M\ge1$, $0<\varepsilon\le1$, and $1<\alpha\le2$. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. The actual composed recurrence uses these ordered slots. At error one the penalty is $+\infty$. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   \log_2M\le\sum_{i=1}^{n}\widehat\Upsilon_\alpha(N^{(i)})+\frac\alpha{\alpha-1}\log_2\frac1{1-\varepsilon}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 15, Unnumbered nonidentical-channel finite-code bound (281)

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

/-- Unnumbered nonidentical-channel finite-code bound (281), arXiv:2010.01058v3, PDF pp.15.
 -/
theorem nonidentical_finiteCode (s : ℕ → Slot) (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (P : AdaptiveCode s n M) (hP : P.Valid) (epsilon alpha : ℝ)
    (hepsilon : 0 < epsilon ∧ epsilon ≤ 1) (halpha : 1 < alpha ∧ alpha ≤ 2)
    (herr : P.ErrorAtMost epsilon false) :
    (Real.logb 2 M : EReal) ≤
      (∑ i : Fin n, upsilon (geometricD alpha) (s i.val).map) + penalty alpha epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
