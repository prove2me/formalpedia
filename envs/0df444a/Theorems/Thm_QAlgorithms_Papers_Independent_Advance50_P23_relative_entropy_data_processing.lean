-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_relative_entropy_data_processing
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.relative_entropy_data_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:50:36.770912+00:00
-- url     : https://prove2.me/theorems/ea33520c-7277-48b0-961f-6c359ed4fac1
-- title:
--   Relative entropy data processing
-- statement:
--   For a finite normalized density matrix $\rho$, positive semidefinite reference $\sigma$, CPTP map $D$, and $-1<s\le1$, $D_{U}(D\rho\|D\sigma)\le D_{U}(\rho\|\sigma)$ and $D_s(D\rho\|D\sigma)\le D_s(\rho\|\sigma)$. The reference need not be normalized; support failure is positive infinity. At $s=0$ the shifted Petz divergence uses Umegaki relative entropy.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 3, Cited (7), (27), (41)–(42): relative-entropy data processing

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF p.3, (7): CPTP data processing for Umegaki and shifted-order Petz
relative entropies. Sigma is positive semidefinite and need not have trace one. -/
theorem relative_entropy_data_processing [Nonempty B] [Nonempty E]
    (rho sigma : Matrix B B ℂ) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef)
    (D : Superop B E) (hD : IsChannel D) (s : ℝ) (hs : s ∈ Set.Ioc (-1 : ℝ) 1) :
    relativeEntropy (D rho) (D sigma) ≤ relativeEntropy rho sigma ∧
    hayashiPetzD s (D rho) (D sigma) ≤ hayashiPetzD s rho sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
