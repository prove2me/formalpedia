-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_degraded_private_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.degraded_private_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:47:44.075738+00:00
-- url     : https://prove2.me/theorems/57c9ec13-fe98-4473-81b1-b50ccecd5717
-- title:
--   Degraded finite cq capacity single-letterization
-- statement:
--   If a CPTP map $D$ satisfies $D(W_{B,x})=W_{E,x}$ for every input, there is an input law $P$ attaining $C=I(P,W_B)-I(P,W_E)$. Every other law has a no larger difference, and for every positive integer $n$, $B_n/n=I(P,W_B)-I(P,W_E)$, with $B_n$ optimizing all finite stochastic auxiliaries.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 14, Unnumbered p.14: degraded-channel single-letter capacity

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

/-- PDF p.14: the cited degraded-channel single-letter capacity and block identity.
The actual degrading CPTP map is a hypothesis; attainment is in the conclusion. -/
theorem degraded_private_capacity [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE)
    (D : Superop B E) (hD : IsChannel D) (hdegraded : ∀ x, D (WB x) = WE x) :
    ∃ P : X → ℝ, IsLaw P ∧
      wiretapCapacity WB WE = (holevo P WB - holevo P WE : ℝ) ∧
      (∀ Q : X → ℝ, IsLaw Q → holevo Q WB - holevo Q WE ≤ holevo P WB - holevo P WE) ∧
      ∀ n : ℕ, 0 < n →
        QAlgorithms.Papers.Independent.Information100.P56.blockPrivate n WB WE / n =
          holevo P WB - holevo P WE := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
