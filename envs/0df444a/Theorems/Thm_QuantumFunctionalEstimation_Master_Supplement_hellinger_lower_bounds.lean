-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_hellinger_lower_bounds
-- name    : QuantumFunctionalEstimation.Master.Supplement.hellinger_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:10:28.589135+00:00
-- url     : https://prove2.me/theorems/de3be73e-7b8c-48be-b879-962d506c4958
-- title:
--   Theorem 5.19 — Hellinger and squared-Hellinger sample lower bounds
-- statement:
--   Let $\rho$ be any unknown $d$-dimensional density matrix. Estimating $d_H(\rho,I_d/d)\text{ and }d_H(\rho,I_d/d)^2$ to additive error $\varepsilon$ with probability at least $2/3$, uniformly on all states, requires $N\ge kR$ samples, where
--   $$R(d,\varepsilon)=\frac{d^2}{\varepsilon^2\log^2d\max\{1,\varepsilon^2\log^2d\}}.$$
--
--   The positive multiplier $k$, error threshold $\varepsilon_0\le1/2$ and integer dimension threshold $d_0\ge2$ are universal and chosen before every $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$. The conclusion holds separately for both distance and squared distance, at the same error $\varepsilon$.
--
--   This companion theorem records the complete application rate; it is not a dependency used to prove the master goal.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 33 (PDF p. 35), Theorem 5.19; alias Theorem 1.8, printed p. 7 (PDF p. 9)

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Theorem 5.19, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem hellinger_lower_bounds :
  ∃ k ε₀ : ℝ, 0 < k ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
  ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    SampleBound (@hellingerToMixed d) ε (k * transitionRate d (ε^2)) ∧
    SampleBound (@hellingerSquaredToMixed d) ε (k * transitionRate d (ε^2)) := by sorry

end QuantumFunctionalEstimation.Master.Supplement
