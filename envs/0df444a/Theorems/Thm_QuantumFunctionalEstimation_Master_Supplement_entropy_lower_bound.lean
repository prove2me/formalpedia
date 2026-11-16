-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_entropy_lower_bound
-- name    : QuantumFunctionalEstimation.Master.Supplement.entropy_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:18.427197+00:00
-- url     : https://prove2.me/theorems/4ab5d3c6-0509-4a3d-924b-c38852c7da1e
-- title:
--   Theorem 5.3 — von Neumann entropy sample and query lower bounds
-- statement:
--   Let $\rho$ be any unknown $d$-dimensional density matrix. Estimating $S(\rho)$ to additive error $\varepsilon$ with probability at least $2/3$, uniformly on all states, requires $N\ge kR$ samples, where
--   $$R(d,\varepsilon)=\frac{d^2}{\varepsilon\log^2d\max\{1,\varepsilon\log^2d\}}+\frac{\log^2d}{\varepsilon^2}.$$
--
--   The positive multiplier $k$, error threshold $\varepsilon_0\le1/2$ and integer dimension threshold $d_0\ge2$ are universal and chosen before every $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$. For every purified state-preparation query estimator, the same regime also has $Q\ge k\sqrt R$, retaining the introductory alias and its logarithmic factors. This includes every environment size $e\ge d$ and every oracle completion of each input.
--
--   This companion theorem records the complete application rate; it is not a dependency used to prove the master goal.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
--   - encoding: introductory purified-query lower bound with displayed or suppressed logarithms → query bound k times the square root of the complete sample rate, using controlled forward and adjoint calls; reason: printed p. 3 (PDF p. 5) gives this lifting; the square root of the complete sample rate is equivalent up to universal factors to the explicitly displayed query rate
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 21 (PDF p. 23), Theorem 5.3; alias Theorem 1.2, printed p. 3 (PDF p. 5)

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Theorem 5.3, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem entropy_lower_bound :
  ∃ k ε₀ : ℝ, 0 < k ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
  ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    EstimationBounds (@entropy d) ε k (entropyRate d ε) := by sorry

end QuantumFunctionalEstimation.Master.Supplement
