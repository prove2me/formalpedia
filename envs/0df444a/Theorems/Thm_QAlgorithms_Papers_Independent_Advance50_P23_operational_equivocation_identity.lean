-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_operational_equivocation_identity
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.operational_equivocation_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:54:09.251989+00:00
-- url     : https://prove2.me/theorems/6b74caf4-edf8-46be-846d-dc42cabbaecb
-- title:
--   Corrected maximum operational equivocation rate
-- statement:
--   For normalized finite cq channels $W_B,W_E$ and a nonnegative rate $R$ above private capacity and at most receiver capacity, let $H_{op}(R)$ be the extended supremum of the existing real limits $\lim_n[\log M_n-I_{mix}(M_n;E^n)]/n$ over actual reliable code sequences of rate $R$. Then $H_{op}(R)=H(R)$, where $H(R)$ is the regularized constrained private-information optimization of (100). The printed infimum is changed to the explicit supremum forced by the source\'s stated maximum and entropy identity. No optimizing sequence or entropy limit is assumed to exist as input.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 17, Corrected (103)

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

/-- PDF p.17, (103). Printed: infimum of conditional-entropy rates. Changed:
supremum, as explicitly specified in operationalEquivocationRate. Why: the source
calls this a maximum on p.2, and its displayed entropy identity uniquely reverses
the leakage infimum in (102). Retain the above-capacity feasible regime of V. -/
theorem operational_equivocation_identity [Nonempty X] [Nonempty B] [Nonempty E]
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (hB : hayashiIsCQ WB) (hE : hayashiIsCQ WE)
    (R : ℝ) (hR : 0 ≤ R) (habove : wiretapCapacity WB WE < (R : EReal))
    (hfeasible : R ≤ receiverCapacity WB) :
    operationalEquivocationRate WB WE R = equivocationFunction R WB WE := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
