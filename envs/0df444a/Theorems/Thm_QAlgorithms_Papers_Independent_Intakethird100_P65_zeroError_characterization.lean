-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_zeroError_characterization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.zeroError_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:43:08.892472+00:00
-- url     : https://prove2.me/theorems/7da70cbd-f740-43ef-9f2b-7ea391b00d30
-- title:
--   Eqs.(19),(20),(30), Remark 1: zero-error cost and regularization
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A\to B$ be CPTP and $t_0(\mathcal N)=\inf\{\operatorname{Tr}V_B:J_{\mathcal N}\le I_A\otimes V_B\}$, with Hermitian $V_B$. Then
--
--   $$S_{\rm NS,0}^{(1)}(\mathcal N)=\log_2\lceil\sqrt{t_0(\mathcal N)}\rceil=\tfrac12 I_{\max}(\mathcal N)+\delta,$$
--   $$\lim_{n\to\infty}\frac1n S_{\rm NS,0}^{(1)}(\mathcal N^{\otimes n})=S_{\rm NS,0}(\mathcal N)=\tfrac12\log_2t_0(\mathcal N)=\tfrac12I_{\max}(\mathcal N).$$
--
--   Here $\delta$ is the computed integer-rounding correction. Zero error is fixed before blocklength tends to infinity. The convergence is asserted, and the regularized quantity is defined through operational zero-error rates.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 7, Eqs.(19),(20),(30), Remark 1: zero-error cost and regularization

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

/-- Eqs.(19),(20),(30) and Remark 1, PDF pp.7--8. Zero error is imposed
before n tends to infinity; the rounded one-shot and regularized costs differ. -/
theorem zeroError_characterization (N : Superop A B) (hN : IsChannel N) :
    oneUseSimulationCost .ns N 0 = roundedTraceCost (zeroTraceValue N) ∧
    oneUseSimulationCost .ns N 0 = channelInfo N / 2 + roundingCorrection (channelInfo N) ∧
    zeroErrorCost N = Real.logb 2 (zeroTraceValue N) / 2 ∧
    zeroErrorCost N = channelInfo N / 2 ∧
    Tendsto (fun n : ℕ => oneUseSimulationCost .ns (channelPower N (n+1)) 0 / (n+1))
      atTop (nhds (zeroErrorCost N)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
