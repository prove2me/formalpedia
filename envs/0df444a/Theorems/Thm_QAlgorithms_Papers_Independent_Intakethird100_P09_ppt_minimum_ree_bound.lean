-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_ppt_minimum_ree_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.ppt_minimum_ree_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:42:12.42363+00:00
-- url     : https://prove2.me/theorems/2c11998a-349d-4601-9811-78938107a24c
-- title:
--   Corollary 3, Eq. (17): minimum of two REE bounds
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state.
--
--   The quantities R, T^infinity and R_H optimize arbitrary finite Bell scenarios and LOCC preprocessing of independent copies, using limsup per positive copy number. Input laws are arbitrary joint laws. T^infinity takes its innermost infimum over a one-copy separable sigma, comparing the same channel and the same measurements on rho^n and sigma^n. R_H counts the successful local-filter branch with its probability, after normalizing that branch; a zero-probability branch scores zero. E_r is the unregularized relative entropy of entanglement. All relative entropies and logarithms use bits and retain infinity on support failure. If rho is PPT, then
--
--   $$R(\rho)\le\min\{E_r(\rho),E_r(\rho^\Gamma)\}.$$
--
--   Both entanglement quantities are computed from the same state. This combines the two relative-entropy bounds.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 4, Corollary 3, Eq. (17): minimum of two REE bounds

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

/-- PDF p.4, Corollary 3, Eq.(17): both REEs are of the same PPT state and its Bob transpose. -/
theorem ppt_minimum_ree_bound (a b : ℕ+) (rho : Op (Fin a × Fin b))
    (hrho : IsDensityMatrix rho) (hppt : (transposeSecond rho).PosSemidef) :
    asymptoticR false rho ≤ min (relativeEntanglement rho)
      (relativeEntanglement (transposeSecond rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
