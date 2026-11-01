-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_threshold_protocol_aborts
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.threshold_protocol_aborts
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:45:20.238042+00:00
-- url     : https://prove2.me/theorems/27abace6-8bc0-40ae-879c-2fd0d627a879
-- title:
--   Unnumbered cryptographic implication: threshold protocols abort
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Fix a state rho, a protocol acceptance predicate on boxes, and a threshold epsilon_v>0. Suppose acceptance implies a signed Bell value at least C(S)+epsilon_v and the proved uniform fixed-state bound is Q_S(rho)<=C(S)+epsilon_0, where epsilon_0<epsilon_v. Then
--
--   $$\forall\text{ complete local POVMs }M,\quad\neg\mathrm{Accept}(P_{\rho,M}).$$
--
--   This is the ideal-statistics abort consequence for that particular threshold protocol. It makes no finite-sample or universal DI-key-capacity claim.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 5, Unnumbered cryptographic implication: threshold protocols abort

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

/-- PDF p.5: a fixed threshold protocol aborts on ideal statistics whose uniform Bell
excess is strictly below its acceptance threshold. No universal DI capacity claim is made. -/
theorem threshold_protocol_aborts (d : ℕ+) (S : BellScenario) (s : BellCoefficients S)
    (rho : Op (Fin d × Fin d)) (hrho : IsDensityMatrix rho)
    (epsilon0 epsilonV : ℝ) (hv : 0 < epsilonV) (hgap : epsilon0 < epsilonV)
    (hbound : stateValue s rho ≤ classicalBound s + epsilon0)
    (accepts : Box (Fin S.nx) (Fin S.ny) (Fin S.na) (Fin S.nb) → Prop)
    (haccept : ∀ P, accepts P → classicalBound s + epsilonV ≤ bellValue s P) :
    ∀ M : Measurements S (Fin d) (Fin d), ¬ accepts (measuredBox M rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
