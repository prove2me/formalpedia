-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_generalized_dephasing_qq
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.generalized_dephasing_qq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:19:36.376994+00:00
-- url     : https://prove2.me/theorems/44e2a8a4-07fd-4d09-8ea3-dc90ac5e67e4
-- title:
--   Theorem 6: generalized-dephasing EPR–GHZ capacity
-- statement:
--   Let $X,C$ be nonempty finite basis sets and let $|\psi_x\rangle^C$ be unit vectors, not necessarily orthogonal. For the isometric broadcast channel $U|x\rangle=|x\rangle^B|\psi_x\rangle^C$, the closed unassisted EPR–GHZ region, in coordinate order $(Q,Q_B)=(\text{GHZ},\text{Alice–Bob EPR})$, equals
--
--   $$Q(U)=\{(Q,Q_B)\ge0:Q_B\le H(X\mid T)_\omega-H(C\mid T)_\omega,\ Q\le I(T;C)_\omega\},$$
--
--   where the union ranges over distributions $p(t,x)$ with $|T|\le|X|$ and $\omega^{TXC}=\bigoplus_{t,x}p(t,x)\psi_x^C$. Entropies are in bits. The operational code has one pure encoding, separate receiver CPTP decoders and a single vanishing joint squared-fidelity error to the product of independent GHZ and EPR states with the source's floor-exponential ranks. This is a single-letter equality; no extra environment is introduced into the entropy difference.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 11, Theorem 6: generalized-dephasing EPR–GHZ capacity

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

/-- Theorem 6, PDF pp.11–12,14: isometric generalized-dephasing EPR–GHZ
capacity. The entropy is H(C|T), and coordinates are (GHZ,EPR_B). -/
theorem generalized_dephasing_qq [Nonempty X] [Nonempty C] (D : DephasingData X C) :
    qqCapacity (conjSuperop D.isometry) = dephasingRegion D (fun rho => rho) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end
