-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_forward_strongConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.forward_strongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:47:57.489801+00:00
-- url     : https://prove2.me/theorems/1a86187b-0ee6-45b6-95ae-162e95760d53
-- title:
--   Theorem 21 (main paper result selected by page-1 seed)
-- statement:
--   Let $N:AB\to A'B'$ be a finite-dimensional bipartite channel. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Write $\widehat\Upsilon$ for the BS-divergence comparison program (161). Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   \widetilde R(N)\le\widehat\Upsilon(N),\qquad C(N)=R(N)\le\widetilde C(N)\le\widetilde R(N)\le\widehat\Upsilon(N)\le C_\beta(N).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Theorem 21 is the unique headline for the page-1 seed; consequences use (265)-(267) and Proposition 15.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 14, Theorem 21 (main paper result selected by page-1 seed)

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

/-- Theorem 21 (main paper result selected by page-1 seed), arXiv:2010.01058v3, PDF pp.1,14,15.
Theorem 21 is the unique headline for the page-1 seed; consequences use (265)-(267) and Proposition 15. -/
theorem forward_strongConverse {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (N : Superop (Fin a × Fin b) (Fin c × Fin d)) (hN : IsChannel N) :
    randomnessStrong N ≤ upsilon bsD N ∧
      forwardCapacity N = randomnessCapacity N ∧
      randomnessCapacity N ≤ classicalStrong N ∧
      classicalStrong N ≤ randomnessStrong N ∧ upsilon bsD N ≤ cBeta N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
