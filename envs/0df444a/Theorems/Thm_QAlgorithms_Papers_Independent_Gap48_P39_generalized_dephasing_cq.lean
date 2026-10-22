-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_generalized_dephasing_cq
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.generalized_dephasing_cq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:16:43.487041+00:00
-- url     : https://prove2.me/theorems/1a6c0b51-4dc0-4030-8355-2e7286f0924a
-- title:
--   Theorem 4: generalized-dephasing classical–quantum capacity
-- statement:
--   Let $X,C,E$ be nonempty finite basis sets and let each $|\psi_x\rangle^{CE}$ be a unit vector, without any orthogonality assumption. Define $U|x\rangle=|x\rangle^B|\psi_x\rangle^{CE}$, with $B$ indexed by $X$, and $\mathcal N=\operatorname{Tr}_E\circ\operatorname{Ad}_U$. Its closed unassisted common-classical/Alice–Bob-EPR capacity region is
--
--   $$CQ(\mathcal N)=\{(R,Q)\ge0:Q\le H(X\mid T)_\omega-H(CE\mid T)_\omega,\ R\le I(T;C)_\omega\},$$
--
--   where the union ranges over distributions $p(t,x)$ with $|T|\le|X|$ and $\omega^{TXCE}=\bigoplus_{t,x}p(t,x)\psi_x^{CE}$. Entropies are in bits; $\psi_x$ denotes the normalized rank-one density matrix. The operational criterion is vanishing maximum joint squared-fidelity error to both common labels and an independent EPR target, with no side communication or preshared resources. Only the dilation $U$ is isometric; $E$ is discarded from $\mathcal N$. This provides an exact single-letter formula while retaining $CE$ jointly in the quantum-rate bound.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 8, Theorem 4: generalized-dephasing classical–quantum capacity

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

/-- Theorem 4, PDF pp.8,10,14: generalized-dephasing CQ capacity, |T|≤|X|.
CE remains joint in the quantum bound; only E is traced for Charlie's information. -/
theorem generalized_dephasing_cq [Nonempty X] [Nonempty C] [Nonempty E]
    (D : DephasingData X (C × E)) :
    cqGenerationCapacity (generalizedDephasingBroadcast D) = dephasingRegion D (traceRight : Superop (C × E) C) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
