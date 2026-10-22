-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_degraded_cq_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.degraded_cq_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:14:13.758218+00:00
-- url     : https://prove2.me/theorems/5e7085eb-3ef5-432e-974a-f46990421f7d
-- title:
--   Theorem 2: degraded cq outer bound and commuting-Bob capacity
-- statement:
--   Let $W:x\mapsto\rho_x^{BC}$ be a finite cq broadcast channel with nonempty alphabet and positive-dimensional outputs. Suppose a CPTP map $\mathcal M:B\to C$ satisfies $\rho_x^C=\mathcal M(\rho_x^B)$ for every input. For the closed operational classical region with deterministic encoders and vanishing maximum joint decoding error,
--
--   $$\mathcal C(W)\subseteq\{(R,R_B,R_C)\ge0:R_B\le I(X;B\mid T)_\sigma,\ R+R_C\le I(T;C)_\sigma\},$$
--
--   where the union ranges over all finite-dimensional quantum auxiliaries $T$ and normalized states $\sigma^{TXBC}=\bigoplus_xp(x)\rho_x^T\otimes\rho_x^{BC}$; no auxiliary dimension cap is imposed on this outer bound. If Bob's marginal states commute pairwise, the two-inequality region with classical $T$, $\sigma=\bigoplus_{t,x}p(t,x)\rho_x^{BC}$, and $|T|\le\min\{|X|,|B|^2\}$ equals $\mathcal C(W)$ and the three-inequality superposition region. Entropies are in bits. This identifies an exact single-letter capacity using only Bob marginal commutation.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 4, Theorem 2: degraded cq outer bound and commuting-Bob capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Theorem 2, PDF p.4 (both columns), converse pp.6–7: unbounded quantum T outer
bound, and exact single-letter region when ONLY Bob's marginals commute. -/
theorem degraded_cq_capacity [Nonempty X] [Nonempty B] [Nonempty C] (W : CQChannel X B C)
    (hW : Degraded W) :
    cqBroadcastCapacity W ⊆ quantumOuterRegion W false ∧
    (CommutingBob W → cqBroadcastCapacity W = degradedClassicalRegion W ∧
      degradedClassicalRegion W = superpositionRegion W (some (superpositionCap X B C))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
