-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_regularized_private_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.regularized_private_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:47:00.210783+00:00
-- url     : https://prove2.me/theorems/c34f5f4e-af85-49e1-afb1-db6016df28bb
-- title:
--   Regularized finite cq private capacity
-- statement:
--   For arbitrary finite nonempty input and output systems and normalized cq families $W_B,W_E$, the real limit $a=\lim_n B_n/n$ exists and $C_{W_B,W_E}=a$, where $B_n$ is the supremum of $I(V;B^n)-I(V;E^n)$ over every finite auxiliary law and stochastic encoder into $X^n$. Capacity is defined by actual codes of positive size, limiting message rate, vanishing average error and vanishing uniform-message Holevo leakage.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 14, Proposition 1, (87): regularized private classical capacity

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

/-- PDF pp.13–14, Proposition 1, (87), attributed to Devetak [7]. The limit
and operational equality are conclusions, with all finite stochastic auxiliaries. -/
theorem regularized_private_capacity [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE) :
    ∃ a : ℝ,
      Tendsto (fun n => QAlgorithms.Papers.Independent.Information100.P56.blockPrivate n WB WE / n)
        atTop (nhds a) ∧ wiretapCapacity WB WE = (a : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
