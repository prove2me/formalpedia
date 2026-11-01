-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_hidden_relative_entropy_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.hidden_relative_entropy_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:42:56.056592+00:00
-- url     : https://prove2.me/theorems/95f07cb0-22bd-4e90-8e37-c3854f8d7370
-- title:
--   Theorem 3, Eqs. (19)–(20): success-weighted hidden nonlocality
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state.
--
--   The quantities R, T^infinity and R_H optimize arbitrary finite Bell scenarios and LOCC preprocessing of independent copies, using limsup per positive copy number. Input laws are arbitrary joint laws. T^infinity takes its innermost infimum over a one-copy separable sigma, comparing the same channel and the same measurements on rho^n and sigma^n. R_H counts the successful local-filter branch with its probability, after normalizing that branch; a zero-probability branch scores zero. E_r is the unregularized relative entropy of entanglement. All relative entropies and logarithms use bits and retain infinity on support failure. For every rho,
--
--   $$R_H(\rho)\le T^\infty(\rho)\le E_r(\rho).$$
--
--   For PPT rho, additionally
--
--   $$R_H(\rho)\le E_r(\rho^\Gamma).$$
--
--   The filter follows LOCC, is a locally realizable selected product Kraus branch of a complete instrument, and its success weight is counted once. This extends the entropy bound to hidden nonlocality.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 4, Theorem 3, Eqs. (19)–(20): success-weighted hidden nonlocality

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

/-- PDF pp.4,9, Theorem 3, Eqs.(19)--(20): filter AFTER LOCC, normalized successful
branch, and success weight counted once. Includes general chain and conditional PPT bound. -/
theorem hidden_relative_entropy_bounds (a b : ℕ+) (rho : Op (Fin a × Fin b))
    (hrho : IsDensityMatrix rho) :
    asymptoticRH false rho ≤ asymptoticT false rho ∧
    asymptoticT false rho ≤ relativeEntanglement rho ∧
    ((transposeSecond rho).PosSemidef →
      asymptoticRH false rho ≤ relativeEntanglement (transposeSecond rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
