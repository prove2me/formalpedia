-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_entanglementBreaking_choi_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.entanglementBreaking_choi_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:10:23.432182+00:00
-- url     : https://prove2.me/theorems/61f4ceca-e85b-4d8b-89e6-04b356bc6973
-- title:
--   Theorem V.2: entanglement-breaking Choi upper bound
-- statement:
--   Let $T:M_{d_A}\to M_{d_B}$ be a quantum channel in positive finite dimensions. For a channel $S$ with the same input and output, write $C_S=(\mathrm{id}\otimes S)(|\Omega\rangle\langle\Omega|)$, where $|\Omega\rangle=d_A^{-1/2}\sum_i|ii\rangle$. Define
--
--   $$B_{\max}(T)=\min_{S\ \mathrm{entanglement\ breaking}}D_{\max}(C_T\|C_S).$$
--
--   The minimum over entanglement-breaking channels is attained, and
--
--   $$E_{\max}(T)\le B_{\max}(T).$$
--
--   Entanglement breaking requires separable output for every normalized bipartite input and every finite reference. In particular, $\operatorname{Tr}_B C_S=I/d_A$ remains fixed.
--
--   This gives a Choi-based bound with the channel marginal constraint preserved.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 17, Theorem V.2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Theorem V.2, PDF p.17: comparison with EB channels, including minimum attainment. -/
theorem entanglementBreaking_choi_bound (T : Superop I J) (hT : IsChannel T) :
    channelEMax T ≤ choiEBBound T ∧
    ∃ S : Superop I J, IsChannel S ∧ BreaksEntanglementAllReferences S ∧
      choiEBBound T = maxRelative (normalizedChannelChoi T) (normalizedChannelChoi S) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
