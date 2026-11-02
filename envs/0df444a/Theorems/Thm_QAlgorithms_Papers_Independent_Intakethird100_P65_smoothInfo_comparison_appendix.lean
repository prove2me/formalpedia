-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_smoothInfo_comparison_appendix
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.smoothInfo_comparison_appendix
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:56:15.722302+00:00
-- url     : https://prove2.me/theorems/c6c2e040-c42c-41e3-868b-a7412a2614a2
-- title:
--   Lemma 9 / Eq.(73): appendix repetition of Lemma 7
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\rho_{AB}$ be a normalized density matrix and $0<\varepsilon<1$. Ordinary smooth max-information optimizes over subnormalized $\widetilde\rho$ at purified distance at most the tolerance and uses $\widetilde\rho_A$ in the reference. Hatted smoothing additionally fixes $\widetilde\rho_A=\rho_A$. Then
--
--   $$\widehat I_{\max}^{\varepsilon}(A:B)_\rho\le I_{\max}^{\varepsilon/6}(A:B)_\rho+\log_2(1+72/\varepsilon^2).$$
--
--   Purified distance uses generalized root fidelity. This compares free and fixed-marginal smoothing without any rank assumption.
--
--   This is the separate numbered occurrence in Appendix B, Lemma 9.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 18, Lemma 9 / Eq.(73): appendix repetition of Lemma 7

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

/-- Lemma 9, Eq.(73), PDF pp.18--19: the numbered appendix occurrence of Lemma 7. -/
theorem smoothInfo_comparison_appendix (rho : Mat (A × B)) (hrho : IsDensityMatrix rho)
    (e : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    fixedSmoothInfo rho e ≤ smoothInfo rho (e/6) + (Real.logb 2 (1 + 72/e^2) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
