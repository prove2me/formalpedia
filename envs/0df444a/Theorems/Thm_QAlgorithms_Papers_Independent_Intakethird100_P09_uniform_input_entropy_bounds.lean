-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_uniform_input_entropy_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.uniform_input_entropy_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:46:17.77844+00:00
-- url     : https://prove2.me/theorems/a6c3a215-290e-4686-810f-6cd04ae0b038
-- title:
--   Appendix: uniform-input versions of Theorems 2 and 3
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Define R_u, T_u^infinity and R_H,u by consistently replacing every joint-input-law optimization in the definitions of R, T^infinity and R_H by the uniform law on that experiment’s finite input alphabet. Keep the same limsup regularization, LOCC class, iid separable reference and normalized success-weighted filter as above. Every regularization uses positive copy numbers and limsup; all logarithms are base two, support violations have infinite relative entropy, and E_r is the unregularized relative entropy distance to normalized separable states. For any state rho,
--
--   $$R_u(\rho)\le T_u^\infty(\rho)\le E_r(\rho),\qquad R_{H,u}(\rho)\le T_u^\infty(\rho).$$
--
--   For PPT rho,
--
--   $$T_u^\infty(\rho)\le E_r(\rho^\Gamma),\qquad R_{H,u}(\rho)\le E_r(\rho^\Gamma).$$
--
--   The optimized and uniform measures are not identified. This records the appendix’s additional uniform-input assertion.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 8, Appendix: uniform-input versions of Theorems 2 and 3

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

/-- PDF pp.8--9: uniform-input variants keep all input-law optimizations uniform,
without identifying them with the optimized measures. Both numbered theorems' chains retained. -/
theorem uniform_input_entropy_bounds (a b : ℕ+) (rho : Op (Fin a × Fin b))
    (hrho : IsDensityMatrix rho) :
    asymptoticR true rho ≤ asymptoticT true rho ∧
    asymptoticRH true rho ≤ asymptoticT true rho ∧
    asymptoticT true rho ≤ relativeEntanglement rho ∧
    ((transposeSecond rho).PosSemidef →
      asymptoticT true rho ≤ relativeEntanglement (transposeSecond rho) ∧
      asymptoticRH true rho ≤ relativeEntanglement (transposeSecond rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
