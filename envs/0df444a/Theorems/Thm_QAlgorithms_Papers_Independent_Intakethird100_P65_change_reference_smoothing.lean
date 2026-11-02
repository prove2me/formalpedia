-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_change_reference_smoothing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.change_reference_smoothing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:56:57.301842+00:00
-- url     : https://prove2.me/theorems/ab385bc2-9dc4-4463-83e5-704987d348d7
-- title:
--   Appendix B / Eq.(78): changing the reference marginal in smoothing
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\rho_{AB}$ be a normalized state and $0<\varepsilon<1$. Define $\widetilde I_{\max}^{\varepsilon}(A:B)_\rho$ by optimizing $D_{\max}(\tau_{AB}\|\rho_A\otimes\sigma_B)$ over subnormalized $\tau$ at purified distance at most $\varepsilon$ and normalized $\sigma_B$. Ordinary smoothing uses $\tau_A$ instead of $\rho_A$. Then
--
--   $$\widetilde I_{\max}^{\varepsilon}(A:B)_\rho\le I_{\max}^{\varepsilon/2}(A:B)_\rho.$$
--
--   No constraint $\tau_A=\rho_A$ is imposed in the tilde quantity. Singular marginals are allowed.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 19, Appendix B / Eq.(78): changing the reference marginal in smoothing

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

/-- Appendix B, Eq.(78), PDF p.19: tilde smoothing versus ordinary smoothing;
no invertibility assumption is added. -/
theorem change_reference_smoothing (rho : Mat (A × B)) (hrho : IsDensityMatrix rho)
    (e : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    referenceSmoothInfo rho e ≤ smoothInfo rho (e/2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
