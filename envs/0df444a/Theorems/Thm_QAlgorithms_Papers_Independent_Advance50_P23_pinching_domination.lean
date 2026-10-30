-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P23_pinching_domination
-- name    : QAlgorithms.Papers.Independent.Advance50.P23.pinching_domination
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:51:20.275669+00:00
-- url     : https://prove2.me/theorems/7324a426-4d25-4afa-a761-253e7bb8ca6b
-- title:
--   Pinching domination
-- statement:
--   For a finite density matrix $\rho$ and positive semidefinite reference $\sigma$, $\rho\preceq v\mathcal E_\sigma(\rho)$, where $\mathcal E_\sigma$ is pinching by distinct eigenspace projections and $v$ is the number of distinct spectral values, including zero when present. The order is Loewner order.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, PDF p. 3, Cited (13): pinching domination

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

/-- PDF p.3, (13): the pinching inequality in Loewner order; v counts distinct
spectral values, not multiplicities. Rho is the normalized state of II.B. -/
theorem pinching_domination [Nonempty E]
    (rho sigma : Matrix E E ℂ) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef) :
    (((eigenCount sigma : ℂ) • pinch sigma rho) - rho).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Advance50.P23

end
