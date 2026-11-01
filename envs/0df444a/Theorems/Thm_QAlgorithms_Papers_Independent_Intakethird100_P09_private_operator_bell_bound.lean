-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_private_operator_bell_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.private_operator_bell_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:40:56.723586+00:00
-- url     : https://prove2.me/theorems/80e2c303-b8bf-4ce3-9a47-cf01fd16153a
-- title:
--   Observation 1: corrected nonnegative-coefficient version
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Let X be an operator on a positive finite bipartite shield with full trace norm one. Suppose sqrt(XX^dagger) and sqrt(X^dagger X) are normalized separable shield states. Define gamma_X exactly by Eq.(7), on the physical key-plus-shield ownership cut. For every nonnegative-coefficient Bell expression,
--
--   $$Q_S(\gamma_X)\le C(S)+Q(S)\|X^\Gamma\|_1.$$
--
--   Here Gamma on X acts only on Bob’s shield. The coefficient is one, without an additional half. This corrected version provides a reusable bound for operator-defined private bits.
--
--   The fixed private-bit formula used here is
--
--   $$\gamma_X=\frac12\left(|00\rangle\langle00|\otimes\sqrt{XX^\dagger}+|00\rangle\langle11|\otimes X+|11\rangle\langle00|\otimes X^\dagger+|11\rangle\langle11|\otimes\sqrt{X^\dagger X}\right),$$
--
--   with the two key qubits and shields regrouped by owner.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 7, Observation 1: corrected nonnegative-coefficient version

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

/-- PDF p.7, Observation 1, Eq.(A.3), CORRECTED s>=0 and Q(gamma_X) to Q_S(gamma_X).
Both square-root shield states are normalized SEP; X has full trace norm one. -/
theorem private_operator_bell_bound (a b : ℕ+) (S : BellScenario) (s : BellCoefficients S)
    (hs : ∀ x y i j, 0 ≤ s x y i j) (X : Op (Fin a × Fin b))
    (hX : traceNorm X = 1) (hleft : IsSeparableDensity (cfc Real.sqrt (X * Xᴴ)))
    (hright : IsSeparableDensity (cfc Real.sqrt (Xᴴ * X))) :
    stateValue s (partyCut (xForm X)) ≤
      classicalBound s + quantumBound s * traceNorm (transposeSecond X) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
