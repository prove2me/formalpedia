-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_nearSep_convex_and_contains
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.nearSep_convex_and_contains
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:36:55.765886+00:00
-- url     : https://prove2.me/theorems/2ebb1586-1770-4227-b79e-b5a0f11195d3
-- title:
--   Unnumbered after Eq. (5): convexity and separable inclusion of D(epsilon)
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Fix a positive local dimension d and epsilon>0. Define
--
--   $$D(\epsilon)=\{\rho:\rho\text{ is a density matrix and }\exists\sigma\in\mathrm{SEP},\ \|\rho^\Gamma-\sigma^\Gamma\|_1\le\epsilon\}.$$
--
--   Then D(epsilon) is convex over the reals and contains SEP. An actual same-dimensional separable witness is required, including on the boundary. These sets organize the single-copy bounds.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 2, Unnumbered after Eq. (5): convexity and separable inclusion of D(epsilon)

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

/-- PDF p.2, following Eq.(5): D(epsilon) is convex and contains every separable density. -/
theorem nearSep_convex_and_contains (d : ℕ+) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Convex ℝ (nearSep (I := Fin d) (J := Fin d) epsilon) ∧
    {rho : Op (Fin d × Fin d) | IsSeparableDensity rho} ⊆ nearSep epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
