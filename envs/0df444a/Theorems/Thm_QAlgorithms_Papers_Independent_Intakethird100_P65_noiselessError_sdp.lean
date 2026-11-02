-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_noiselessError_sdp
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.noiselessError_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:41:20.063459+00:00
-- url     : https://prove2.me/theorems/e24505a4-184a-4438-b905-db9d121739fe
-- title:
--   Corollary 2 / SDP (9): noiseless-resource reduced minimum error
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A\to B$ be CPTP and let $m\ge1$ be an integer. Put $\omega_\Omega(\mathrm{id}_m,\mathcal N)$ for the minimum half-diamond error using one noiseless $m$-dimensional resource. Then
--
--   $$\omega_{\rm NS}(\mathrm{id}_m,\mathcal N)=\inf\gamma$$
--
--   subject to $Y\ge J- J_{\mathcal N}$, $Y\ge0$, $\operatorname{Tr}_B Y\le\gamma I_A$, $J\ge0$, $\operatorname{Tr}_B J=I_A$, $J\le I_A\otimes V_B$, and $\operatorname{Tr}V_B=m^2$. All $Y,J,V_B$ are bound Hermitian optimization variables. For NS-intersect-PPT assistance add $-I_A\otimes V_B^T\le mJ^{T_B}\le I_A\otimes V_B^T$. This reduction includes $m=1$, where feasible effective channels are constant.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 5, Corollary 2 / SDP (9): noiseless-resource reduced minimum error

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

/-- Corollary 2, SDP (9), PDF pp.5--6. Resource dimension m=1 is included. -/
theorem noiselessError_sdp (N : Superop A B) (hN : IsChannel N) (m : ℕ) (hm : 0 < m) :
    minimumError .ns (fun X : Mat (Fin m) => X) N =
      sInf {g : ℝ | reducedErrorFeasible false N m g} ∧
    minimumError .nsPpt (fun X : Mat (Fin m) => X) N =
      sInf {g : ℝ | reducedErrorFeasible true N m g} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
