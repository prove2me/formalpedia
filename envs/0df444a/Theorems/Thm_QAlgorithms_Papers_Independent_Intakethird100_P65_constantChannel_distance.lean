-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_constantChannel_distance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.constantChannel_distance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:44:51.919827+00:00
-- url     : https://prove2.me/theorems/a53d9226-a7cc-4a2c-aed6-a6ccc864c71e
-- title:
--   Remark 6 / Eq.(36): distance to constant channels
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A\to B$ be CPTP and $\varepsilon\ge0$. Let $\mathcal G$ consist of all replacement channels $\mathcal R_\sigma(X)=\operatorname{Tr}(X)\sigma$, where $\sigma$ is a density matrix on $B$. Define $D_{\max}^\varepsilon(\mathcal N\|\mathcal M)$ by smoothing only $\mathcal N$ over same-dimensional CPTP channels at half-diamond distance at most $\varepsilon$, and using the max-relative entropy of unnormalized Choi matrices. Then
--
--   $$I_{\max}^\varepsilon(\mathcal N)=\min_{\mathcal M\in\mathcal G}D_{\max}^\varepsilon(\mathcal N\|\mathcal M).$$
--
--   A minimizing constant channel exists and has value no larger than every other constant reference. Extended-real divergences retain support failures.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 9, Remark 6 / Eq.(36): distance to constant channels

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

/-- Remark 6, Eq.(36), PDF p.9: equality to a MINIMUM, including attainment. -/
theorem constantChannel_distance (N : Superop A B) (hN : IsChannel N) (e : ℝ) (he : 0 ≤ e) :
    ∃ M : Superop A B, Constant M ∧
      smoothChannelDmax N M e = (smoothChannelInfo N e : EReal) ∧
      ∀ T : Superop A B, Constant T → smoothChannelDmax N M e ≤ smoothChannelDmax N T e := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
