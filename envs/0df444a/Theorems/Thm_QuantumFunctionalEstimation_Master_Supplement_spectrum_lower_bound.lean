-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_spectrum_lower_bound
-- name    : QuantumFunctionalEstimation.Master.Supplement.spectrum_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:08:19.894198+00:00
-- url     : https://prove2.me/theorems/21cd1ea3-95a4-4815-a451-18d67b3c5f1a
-- title:
--   Theorem 5.15 — ordered-spectrum sample lower bound
-- statement:
--   Let $\rho$ be any unknown $d$-dimensional density matrix. Estimating $\lambda^\downarrow(\rho)$ to additive error $\varepsilon$ with probability at least $2/3$, uniformly on all states, requires $N\ge kR$ samples, where
--   $$R(d,\varepsilon)=\frac{d^2}{\varepsilon^2\log^2d\max\{1,\varepsilon^2\log^2d\}}.$$
--
--   The positive multiplier $k$, error threshold $\varepsilon_0\le1/2$ and integer dimension threshold $d_0\ge2$ are universal and chosen before every $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$. Spectrum error is total variation against the decreasing ordered spectrum; outputs range over all real vectors, without a sorting or probability-vector requirement.
--
--   This companion theorem records the complete application rate; it is not a dependency used to prove the master goal.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 31 (PDF p. 33), Theorem 5.15; alias Theorem 1.6, printed p. 6 (PDF p. 8)

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Theorem 5.15, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem spectrum_lower_bound :
  ∃ k ε₀ : ℝ, 0 < k ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
  ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ N : ℕ, ∀ E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin d) (Fin d → ℝ),
      SpectrumSuccessful d N ε E → k * transitionRate d (ε^2) ≤ N := by sorry

end QuantumFunctionalEstimation.Master.Supplement
