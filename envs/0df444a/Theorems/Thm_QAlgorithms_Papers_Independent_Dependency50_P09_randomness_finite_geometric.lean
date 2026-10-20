-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_randomness_finite_geometric
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.randomness_finite_geometric
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:02:18.685198+00:00
-- url     : https://prove2.me/theorems/c3505a45-6cb0-4faa-bbdd-1a84dedb97a4
-- title:
--   Theorem 20
-- statement:
--   Let $N$ be bipartite CPTP, $n\ge1$, $0\le\varepsilon<1$, and $1<\alpha\le2$. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   R^{n,\varepsilon}(N)\le\widehat\Upsilon_\alpha(N)+\frac\alpha{n(\alpha-1)}\log_2\frac1{1-\varepsilon}.
--   $$
--
--   This gives the source's operational capacity conclusion in the stated assistance model.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 14, Theorem 20

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

/-- Theorem 20, arXiv:2010.01058v3, PDF pp.14.
 -/
theorem randomness_finite_geometric {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (N : Superop (Fin a × Fin b) (Fin c × Fin d)) (hN : IsChannel N)
    (n : ℕ) (hn : 0 < n) (epsilon alpha : ℝ)
    (hepsilon : 0 ≤ epsilon ∧ epsilon < 1)
    (halpha : 1 < alpha ∧ alpha ≤ 2) :
    finiteCapacity N n epsilon true ≤ upsilon (geometricD alpha) N +
      (((1 : ℝ)/n : ℝ) : EReal) * penalty alpha epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
