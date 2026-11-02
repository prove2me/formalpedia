-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_smooth_robustness_identity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.smooth_robustness_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:45:43.00221+00:00
-- url     : https://prove2.me/theorems/2117e757-01fc-45f2-9842-2c2eb02c48ae
-- title:
--   Remark 6 / Eq.(40): smooth generalized channel robustness
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   For a CPTP channel $\mathcal N:A\to B$, define independently $R_g(\mathcal N)=\inf\{t\ge0:\exists\mathcal M\text{ CPTP},\ (\mathcal N+t\mathcal M)/(1+t)\in\mathcal G\}$, where $\mathcal G$ is the set of replacement channels. Smooth this robustness over CPTP alternatives at half-diamond distance at most $\varepsilon\ge0$, obtaining $R_g^\varepsilon(\mathcal N)$. Then
--
--   $$I_{\max}^\varepsilon(\mathcal N)=\log_2(1+R_g^\varepsilon(\mathcal N)).$$
--
--   The mixing channel may be any CPTP map. This relates the independently defined channel entropy and generalized robustness.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 9, Remark 6 / Eq.(40): smooth generalized channel robustness

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

/-- Remark 6, Eq.(40), PDF pp.9--10: independent generalized constantChannelRobustness,
with arbitrary CPTP mixing noise. -/
theorem smooth_robustness_identity (N : Superop A B) (hN : IsChannel N)
    (e : ℝ) (he : 0 ≤ e) :
    smoothChannelInfo N e = Real.logb 2 (1 + smoothRobustness N e) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
