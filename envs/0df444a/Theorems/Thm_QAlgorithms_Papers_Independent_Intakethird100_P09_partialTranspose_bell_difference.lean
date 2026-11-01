-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_partialTranspose_bell_difference
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.partialTranspose_bell_difference
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:34:56.695584+00:00
-- url     : https://prove2.me/theorems/63c6c293-094f-4dfc-9a6f-ad8f0df88817
-- title:
--   Theorem 1, Eq. (1): partial-transpose Bell-value difference
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Let rho and sigma have the same positive local dimension d, and fix the same local POVMs for both. Write S_M for the resulting Bell operator and S_M(rho) for its expectation. Then
--
--   $$|S_M(\rho)-S_M(\sigma)|\le\|S_M^\Gamma\|_\infty\,\|\rho^\Gamma-\sigma^\Gamma\|_1.$$
--
--   The coefficients may be signed, and neither state needs to be PPT. This relates a fixed Bell-value difference to distinguishability after transposition.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 2, Theorem 1, Eq. (1): partial-transpose Bell-value difference

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

/-- PDF pp.2,6, Theorem 1, Eq.(1): general real Bell coefficients, fixed common POVMs.
Neither state is assumed PPT; the full trace norm is used. -/
theorem partialTranspose_bell_difference (d : ℕ+) (S : BellScenario) (s : BellCoefficients S)
    (rho sigma : Op (Fin d × Fin d)) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) (M : Measurements S (Fin d) (Fin d)) :
    |bellValue s (measuredBox M rho) - bellValue s (measuredBox M sigma)| ≤
      bellOperatorNorm (transposeSecond (bellOperator s M)) *
        traceNorm (transposeSecond rho - transposeSecond sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
