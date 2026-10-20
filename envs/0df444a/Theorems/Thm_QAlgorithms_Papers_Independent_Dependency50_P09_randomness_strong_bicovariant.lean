-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_randomness_strong_bicovariant
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.randomness_strong_bicovariant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:07:10.628766+00:00
-- url     : https://prove2.me/theorems/4b48847b-c3a4-417f-b2c8-98164769690b
-- title:
--   Corollary 29
-- statement:
--   Let $N$ be a bipartite channel covariant under two independent input unitary one-designs, with matching unitary output representations. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Here $\Upsilon$ uses the unaccented Umegaki relative entropy. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   \widetilde R(N)\le\Upsilon(N).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 18, Corollary 29

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

/-- Corollary 29, arXiv:2010.01058v3, PDF pp.18.
 -/
theorem randomness_strong_bicovariant {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (N : Superop (Fin a × Fin b) (Fin c × Fin d)) (hN : IsChannel N)
    (hcov : HasBiDesign N) :
    randomnessStrong N ≤ upsilon relativeD N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
