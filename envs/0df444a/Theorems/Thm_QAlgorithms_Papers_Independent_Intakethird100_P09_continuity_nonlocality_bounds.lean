-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_continuity_nonlocality_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.continuity_nonlocality_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:43:38.975174+00:00
-- url     : https://prove2.me/theorems/b6810921-26d3-49f9-8933-5ee69a81adc9
-- title:
--   Application Eq. (21): continuity-based R and R_H bounds
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state.
--
--   The quantities R, T^infinity and R_H optimize arbitrary finite Bell scenarios and LOCC preprocessing of independent copies, using limsup per positive copy number. Input laws are arbitrary joint laws. T^infinity takes its innermost infimum over a one-copy separable sigma, comparing the same channel and the same measurements on rho^n and sigma^n. R_H counts the successful local-filter branch with its probability, after normalizing that branch; a zero-probability branch scores zero. E_r is the unregularized relative entropy of entanglement. All relative entropies and logarithms use bits and retain infinity on support failure. Let rho be PPT on local dimensions a,b>=1 and belong to D(epsilon), with 0<epsilon<1/2 and an actual separable witness for that membership. Membership in D(epsilon) means that a normalized separable sigma on the same space satisfies ||rho^Gamma-sigma^Gamma||_1<=epsilon. Write d=ab for TOTAL bipartite dimension and h(epsilon)=-epsilon log_2(epsilon)-(1-epsilon)log_2(1-epsilon). Then
--
--   $$R(\rho)\le4\epsilon\log_2d+2h(\epsilon),\qquad R_H(\rho)\le4\epsilon\log_2d+2h(\epsilon).$$
--
--   The PPT standing condition is retained from the invoked corollary. This makes both asymptotic measures small near the transposed separable set.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 4, Application Eq. (21): continuity-based R and R_H bounds

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

/-- PDF p.4, Eq.(21): standing PPT condition retained from Corollary 3.
Dimension is TOTAL bipartite dimension, logs in bits, source constant 4. -/
theorem continuity_nonlocality_bounds (a b : ℕ+) (rho : Op (Fin a × Fin b))
    (hppt : (transposeSecond rho).PosSemidef) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hsmall : epsilon < 1/2) (hnear : rho ∈ nearSep epsilon) :
    let bound := ENNReal.ofReal (4 * epsilon * (Real.log ((a : ℝ) * (b : ℝ)) / Real.log 2) +
      2 * binEntropy2 epsilon)
    asymptoticR false rho ≤ bound ∧ asymptoticRH false rho ≤ bound := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
