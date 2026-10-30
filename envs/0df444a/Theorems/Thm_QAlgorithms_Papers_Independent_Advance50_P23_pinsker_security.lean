-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_pinsker_security
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.pinsker_security
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:51:58.961308+00:00
-- url     : https://prove2.me/theorems/9f7e5ce3-888a-42ff-ad71-8042b31307f1
-- title:
--   Pinsker security comparisons
-- statement:
--   For every normalized finite cq family $W$, $d_{1,mix}(W)^2\le2 I_{mix}(W)$ and $d_{1,max}(W)^2\le2 I_{max}(W)$. The first pair uses uniform inputs and the second pair maximizes over all normalized input laws; logarithms are natural and the distances use the full trace norm.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 6, Cited (48)–(49): quantum Pinsker security comparisons

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

/-- PDF p.6, (48)–(49): quantum Pinsker comparisons for the full trace norm
and natural logarithms, for both uniform-message and source-universal metrics. -/
theorem pinsker_security [Nonempty X] [Nonempty E]
    (W : X → Matrix E E ℂ) (hW : hayashiIsCQ W) :
    (d1mix W)^2 ≤ 2 * Imix W ∧ (d1max W)^2 ≤ 2 * Imax W := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
