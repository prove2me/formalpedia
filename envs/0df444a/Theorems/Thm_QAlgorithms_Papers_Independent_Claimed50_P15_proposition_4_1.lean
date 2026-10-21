-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_4_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_4_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:47:39.86456+00:00
-- url     : https://prove2.me/theorems/1f2401cf-548e-40a0-bfb2-1eae893bec46
-- title:
--   Proposition 4.1
-- statement:
--   Let $Q_m$ be finite nonzero quantum systems with self-adjoint Hamiltonians and faithful normalized states, with physical two-measurement FCS $P_{mt}$ and Petz entropic functions $e_{mt}$. Assume TD: an open interval $I$ containing $[0,1]$ is symmetric about $1/2$, and for every fixed $t>0$ the finite limit $e_t(s)=\lim_m e_{mt}(s)$ exists for every $s\in I$. There are Borel probability measures $P_t$ such that, on the complex strip $\operatorname{Re}z\in I$,
--
--   $$\lim_{m\to\infty}\int e^{-tz\phi}\,dP_{mt}(\phi)=\int e^{-tz\phi}\,dP_t(\phi),\qquad P_{mt}\Rightarrow P_t,\qquad e^{-t\phi}dP_{mt}\Rightarrow e^{-t\phi}dP_t.$$
--
--   The limiting complex integrands are integrable. Time is fixed before the thermodynamic limit, and weak convergence is tested against all bounded continuous functions.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 24, Proposition 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 4.1, arXiv:1109.3804v2, PDF p.24.
The complex strip, probability property and both weak limits are retained.
Time is fixed before the thermodynamic index tends to infinity. -/
theorem proposition_4_1 (Q : ℕ → FiniteSystem) (I : Set ℝ) (hTD : HasTD Q I) :
    ∀ t : ℝ, 0 < t →
      IsProbabilityMeasure (tdFCS Q t) ∧
      (∀ z : ℂ, z.re ∈ I →
        Integrable (fun phi : ℝ => Complex.exp (-(t : ℂ) * z * (phi : ℂ))) (tdFCS Q t) ∧
        Tendsto (fun m => ∫ phi : ℝ, Complex.exp (-(t : ℂ) * z * (phi : ℂ))
          ∂finiteFCS (Q m).H (Q m).omega t) atTop
            (nhds (∫ phi : ℝ, Complex.exp (-(t : ℂ) * z * (phi : ℂ)) ∂tdFCS Q t))) ∧
      WeakMeasureLimit (fun m => finiteFCS (Q m).H (Q m).omega t) atTop (tdFCS Q t) ∧
      WeakMeasureLimit (fun m => (finiteFCS (Q m).H (Q m).omega t).withDensity
        (fun phi => ENNReal.ofReal (Real.exp (-t * phi)))) atTop
          ((tdFCS Q t).withDensity (fun phi => ENNReal.ofReal (Real.exp (-t * phi)))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
