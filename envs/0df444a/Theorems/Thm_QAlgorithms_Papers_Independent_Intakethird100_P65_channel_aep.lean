-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_channel_aep
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.channel_aep
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:48:11.507382+00:00
-- url     : https://prove2.me/theorems/ee5a25de-c8e6-49a5-8815-43fe7763fd3a
-- title:
--   Theorem 8 / Eq.(48): channel asymptotic equipartition property
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   For every CPTP channel $\mathcal N:A'\to B$, let $I(\mathcal N)$ be the maximum state mutual information over all purified input density matrices, including singular ones. Then
--
--   $$\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}\frac1n I_{\max}^{\varepsilon}(\mathcal N^{\otimes n})=I(\mathcal N).$$
--
--   The inner limits exist for every $0<\varepsilon<1$, and the outer limit approaches zero from above. A maximizing input density for $I(\mathcal N)$ exists. This is the channel asymptotic equipartition property.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 11, Theorem 8 / Eq.(48): channel asymptotic equipartition property

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

/-- Theorem 8, Eq.(48), PDF pp.11--12: successive limits in the printed order,
with existence of the inner limits. No full-rank restriction on the optimizer. -/
theorem channel_aep (N : Superop A B) (hN : IsChannel N) :
    IteratedLimit (fun e n => smoothChannelInfo (channelPower N n) e / n)
      (channelMutualInfo N) ∧
    (∃ rho : Mat A, IsDensityMatrix rho ∧
      quantumMutualInformation (idTensorSuperop N (purify rho)) = channelMutualInfo N) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
