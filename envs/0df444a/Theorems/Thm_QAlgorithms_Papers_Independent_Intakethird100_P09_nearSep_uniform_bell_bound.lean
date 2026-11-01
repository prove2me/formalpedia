-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_nearSep_uniform_bell_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.nearSep_uniform_bell_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:37:57.595814+00:00
-- url     : https://prove2.me/theorems/049bdd7b-8e60-4473-972c-0dd622363444
-- title:
--   Corollary 2: corrected nonnegative-coefficient version
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Fix positive local dimension d, epsilon>0, and nonnegative Bell coefficients. Define D(epsilon) using normalized states with an actual separable witness sigma satisfying the full-norm bound on their partial transposes. Then
--
--   $$\sup_{\rho\in D(\epsilon)}Q_S(\rho)\le C(S)+\epsilon Q(S).$$
--
--   The state supremum has this fixed dimension, while Q(S) remains dimension-unrestricted. This corrected nonnegative-coefficient version gives a uniform bound for the near-separable set.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 3, Corollary 2: corrected nonnegative-coefficient version

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

/-- PDF p.3, Corollary 2, Eq.(6), CORRECTED to nonnegative Bell coefficients.
Dimension is fixed before taking the state supremum; Q(S) remains unrestricted. -/
theorem nearSep_uniform_bell_bound (d : ℕ+) (S : BellScenario) (s : BellCoefficients S)
    (hs : ∀ x y a b, 0 ≤ s x y a b) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    sSup {v : ℝ | ∃ rho : Op (Fin d × Fin d), rho ∈ nearSep epsilon ∧
      v = stateValue s rho} ≤ classicalBound s + epsilon * quantumBound s := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
