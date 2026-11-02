-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_minimumError_sdp
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.minimumError_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:40:26.367285+00:00
-- url     : https://prove2.me/theorems/18e39ab5-742b-485f-9514-7e9bb33c8ddf
-- title:
--   Proposition 1 / SDP (6): NS and NS∩PPT minimum simulation error
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A_o\to B_i$ and $\mathcal M:A_i\to B_o$ be CPTP maps. Let $\omega_\Omega(\mathcal N,\mathcal M)$ be the infimum half-diamond simulation error over codes with assistance $\Omega$. For a Hermitian matrix $Z$ on $(A_iB_i)(A_oB_o)$ define $J_{\rm eff}=\operatorname{Tr}_{A_oB_i}[(J_{\mathcal N}^{T}\otimes I_{A_iB_o})Z]$, with registers reordered as indicated. Then
--
--   $$\omega_{\rm NS}(\mathcal N,\mathcal M)=\inf\{\gamma:\operatorname{Tr}_{B_o}Y\le\gamma I_{A_i},\ Y\ge J_{\rm eff}-J_{\mathcal M},\ Y\ge0,\ Z\text{ satisfies (6e)--(6g)}\}.$$
--
--   The explicitly encoded constraints (6e)--(6g) are $Z\ge0$, $\operatorname{Tr}_{A_oB_o}Z=I_{A_iB_i}$, $\operatorname{Tr}_{A_o}Z=(I_{A_i}/|A_i|)\otimes\operatorname{Tr}_{A_oA_i}Z$, and $\operatorname{Tr}_{B_o}Z=(I_{B_i}/|B_i|)\otimes\operatorname{Tr}_{B_iB_o}Z$. The infimum ranges over all $\gamma,Y,Z$. Adding $Z^{T_{B_iB_o}}\ge0$ gives exactly $\omega_{\rm NS\cap PPT}$. This characterizes noisy-resource simulation by matrix optimization.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 4, Proposition 1 / SDP (6): NS and NS∩PPT minimum simulation error

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Proposition 1, SDP (6), PDF p.4. Both NS and NS-intersect-PPT conclusions. -/
theorem minimumError_sdp (N : Superop B C) (M : Superop A D)
    (hN : IsChannel N) (hM : IsChannel M) :
    minimumError .ns N M = sInf {g : ℝ | generalErrorFeasible false N M g} ∧
    minimumError .nsPpt N M = sInf {g : ℝ | generalErrorFeasible true N M g} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
