-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_fixedMarginal_continuity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.fixedMarginal_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:59:16.851199+00:00
-- url     : https://prove2.me/theorems/37a2f3d3-e208-40ed-a423-36873863ff07
-- title:
--   Lemma 12 / Eq.(97): fixed-marginal mutual-information continuity
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\rho_{AB},\sigma_{AB}$ be normalized density matrices with $\rho_A=\sigma_A$, and let $\varepsilon\ge0$ satisfy $\tfrac12\|\rho-\sigma\|_1\le\varepsilon$. Then
--
--   $$|I(A:B)_\rho-I(A:B)_\sigma|\le2\varepsilon\log_2|A|+(1+\varepsilon)h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right).$$
--
--   Here $h_2$ is binary entropy in bits. The dimension is that of the fixed reference system $A$, and singular states are permitted.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 21, Lemma 12 / Eq.(97): fixed-marginal mutual-information continuity

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

/-- Lemma 12, Eq.(97), PDF p.21: fixed A marginal, half trace distance,
log dimension of A, and epsilon/(1+epsilon). -/
theorem fixedMarginal_continuity (rho sigma : Mat (A × B))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hmarg : traceRight rho = traceRight sigma) (e : ℝ) (he : 0 ≤ e)
    (hdist : traceNorm (rho - sigma) / 2 ≤ e) :
    |quantumMutualInformation rho - quantumMutualInformation sigma| ≤
      2*e*Real.logb 2 (Fintype.card A) + (1+e)*binEntropy2 (e/(1+e)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
