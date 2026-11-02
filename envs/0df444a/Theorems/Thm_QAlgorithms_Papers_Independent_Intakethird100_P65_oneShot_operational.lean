-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_oneShot_operational
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.oneShot_operational
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:39:26.845212+00:00
-- url     : https://prove2.me/theorems/3076bd1e-3925-4796-9dca-bf98897fb39d
-- title:
--   Theorem 6 / Eq.(32): exact one-shot operational interpretation
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A'\to B$ be a quantum channel and $\varepsilon\ge0$. Write $I_{\max}^\varepsilon(\mathcal N)$ for the infimum of the channel max-information over CPTP maps $\widetilde{\mathcal N}:A'\to B$ with $\frac12\|\widetilde{\mathcal N}-\mathcal N\|_\diamond\le\varepsilon$. Let $S_{\mathrm{NS},\varepsilon}^{(1)}$ be the minimum binary logarithm of an integer noiseless resource dimension, using one channel use and a bipartite CPTP code that is no-signalling in both directions. Then
--
--   $$S_{\mathrm{NS},\varepsilon}^{(1)}(\mathcal N)=\log_2\left\lceil 2^{I_{\max}^\varepsilon(\mathcal N)/2}\right\rceil=\tfrac12I_{\max}^\varepsilon(\mathcal N)+\delta.$$
--
--   Here $\delta=\log_2\lceil2^{I_{\max}^\varepsilon(\mathcal N)/2}\rceil-I_{\max}^\varepsilon(\mathcal N)/2$ belongs to $[0,1]$ and is the least nonnegative correction that makes the right-hand side the logarithm of a positive integer. This is the exact one-shot operational interpretation, including zero error and tolerances at least one.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 8, Theorem 6 / Eq.(32): exact one-shot operational interpretation

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

/-- Theorem 6, Eq.(32), PDF pp.8--9; ceiling form in Remark 4, p.9.
The rounding correction is computed and is the least nonnegative one. -/
theorem oneShot_operational (N : Superop A B) (hN : IsChannel N) (e : ℝ) (he : 0 ≤ e) :
    oneUseSimulationCost .ns N e = roundedInfoCost (smoothChannelInfo N e) ∧
    oneUseSimulationCost .ns N e = smoothChannelInfo N e / 2 + roundingCorrection (smoothChannelInfo N e) ∧
    0 ≤ roundingCorrection (smoothChannelInfo N e) ∧
    roundingCorrection (smoothChannelInfo N e) ≤ 1 ∧
    (∀ delta : ℝ, 0 ≤ delta →
      (∃ m : ℕ, 0 < m ∧ smoothChannelInfo N e / 2 + delta = Real.logb 2 m) →
      roundingCorrection (smoothChannelInfo N e) ≤ delta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
