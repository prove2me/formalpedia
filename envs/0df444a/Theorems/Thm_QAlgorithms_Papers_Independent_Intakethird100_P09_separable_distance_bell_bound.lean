-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_separable_distance_bell_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.separable_distance_bell_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:35:54.165794+00:00
-- url     : https://prove2.me/theorems/cec39d6e-2e1d-4586-a068-2eb33afa5de6
-- title:
--   Corollary 1: corrected nonnegative-coefficient version
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Assume every coefficient of S is nonnegative and rho has positive equal local dimensions. Let SEP denote the normalized separable states on that same space. Then
--
--   $$Q_S(\rho)\le C(S)+Q(S)\inf_{\sigma\in\mathrm{SEP}}\|\rho^\Gamma-\sigma^\Gamma\|_1=C(S)+Q(S)\inf_{\sigma\in\mathrm{SEP}}\|\rho^\Gamma-\sigma\|_1.$$
--
--   The equality of the two infima is included. This is an explicitly corrected restriction of the printed unrestricted claim; it bounds fixed-state nonlocality by distance to SEP.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 2, Corollary 1: corrected nonnegative-coefficient version

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Entanglement (IsSeparableDensity)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (transposeSecond partyCut xForm swapPrivate hidingOne hidingTwo)

open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Advance50.P47 (Box)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntanglement)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.2,6--7, Corollary 1, Eq.(4), CORRECTED domain: all coefficients nonnegative.
Printed unrestricted signed formula is false. Also retains the equivalent untransposed-SEP form. -/
theorem separable_distance_bell_bound (d : ℕ+) (S : BellScenario) (s : BellCoefficients S)
    (hs : ∀ x y a b, 0 ≤ s x y a b) (rho : Op (Fin d × Fin d))
    (hrho : IsDensityMatrix rho) :
    stateValue s rho ≤ classicalBound s + quantumBound s * sepDistance rho ∧
    sepDistance rho = sepDistanceUntransposed rho ∧
    stateValue s rho ≤ classicalBound s + quantumBound s * sepDistanceUntransposed rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
