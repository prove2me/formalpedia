-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_capacity_comparison_expurgation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.capacity_comparison_expurgation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:14:57.086505+00:00
-- url     : https://prove2.me/theorems/bb5c5e7e-a8b7-4966-9593-42ab87bba199
-- title:
--   Unnumbered capacity comparison and expurgation (263)–(267)
-- statement:
--   Let $N$ be a bipartite channel, $n\ge1$, and $0\le\varepsilon\le1/2$. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. At $\varepsilon=1/2$ the expurgated error is one; the operational supremum at error one is $+\infty$. No equality of the two strong-converse capacities is asserted. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   C^{n,\varepsilon}(N)\le R^{n,\varepsilon}(N),\qquad R^{n,\varepsilon}(N)-\frac1n\le C^{n,2\varepsilon}(N),\qquad C(N)=R(N)\le\widetilde C(N)\le\widetilde R(N).
--   $$
--
--   This gives the source's operational capacity conclusion in the stated assistance model.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 14, Unnumbered capacity comparison and expurgation (263)–(267)

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

/-- Unnumbered capacity comparison and expurgation (263)–(267), arXiv:2010.01058v3, PDF pp.14.
 -/
theorem capacity_comparison_expurgation {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (N : Superop (Fin a × Fin b) (Fin c × Fin d)) (hN : IsChannel N)
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon ∧ epsilon ≤ 1/2) :
    finiteCapacity N n epsilon false ≤ finiteCapacity N n epsilon true ∧
      finiteCapacity N n epsilon true - (((1 : ℝ)/n : ℝ) : EReal) ≤
        finiteCapacity N n (2*epsilon) false ∧
      forwardCapacity N = randomnessCapacity N ∧
      randomnessCapacity N ≤ classicalStrong N ∧ classicalStrong N ≤ randomnessStrong N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
