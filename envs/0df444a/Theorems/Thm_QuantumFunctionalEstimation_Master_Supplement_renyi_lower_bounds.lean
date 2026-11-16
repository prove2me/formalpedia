-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_renyi_lower_bounds
-- name    : QuantumFunctionalEstimation.Master.Supplement.renyi_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:17.62272+00:00
-- url     : https://prove2.me/theorems/d119b970-426a-40c5-8edd-ec42f7a14e3e
-- title:
--   Theorem 5.9 — Rényi entropy sample and query lower bounds, both regimes
-- statement:
--   Let $\rho$ be any unknown $d$-dimensional density matrix. Estimating $S^R_\alpha(\rho)$ to additive error $\varepsilon$ with probability at least $2/3$, uniformly on all states, requires $N\ge kR$ samples, where
--   $$R_\alpha(d,\varepsilon)=\begin{cases}\dfrac{d^{1+1/\alpha}}{\varepsilon^{1/\alpha}\log^2d\max\{1,\varepsilon^{1/\alpha}\log^2d\}}+\dfrac{d^{1/\alpha-1}}{\varepsilon^2},&0<\alpha<1,\\\dfrac{d^2}{\varepsilon^{1/\alpha}\log^{\kappa_\alpha}d}+\dfrac{d^{1-1/\alpha}}{\varepsilon^2},&\alpha>1\text{ noninteger},\end{cases}\quad\kappa_\alpha=\frac{4\lceil\alpha\rceil}{\lceil\alpha\rceil-\alpha}.$$
--
--   For each fixed allowed $\alpha$, choose $k>0$, $\varepsilon_0\in(0,1/2]$ and $d_0\ge2$ depending only on $\alpha$, before all $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$. For every purified state-preparation query estimator, the same regime also has $Q\ge k\sqrt R$, retaining the introductory alias and its logarithmic factors. This includes every environment size $e\ge d$ and every oracle completion of each input.
--
--   This companion theorem records the complete application rate; it is not a dependency used to prove the master goal.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
--   - encoding: introductory purified-query lower bound with displayed or suppressed logarithms → query bound k times the square root of the complete sample rate, using controlled forward and adjoint calls; reason: printed p. 3 (PDF p. 5) lifts the complete sample rate; its square root supplies explicit logarithmic factors and implies the introductory tilde-Omega announcement
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 25–26 (PDF p. 27–28), Theorem 5.9; alias Theorem 1.3, printed p. 4 (PDF p. 6)

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Theorem 5.9, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem renyi_lower_bounds :
  ∀ α : ℝ, 0 < α → Noninteger α →
  ∃ k ε₀ : ℝ, 0 < k ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
  ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    EstimationBounds (@renyi d α) ε k (renyiRate α d ε) := by sorry

end QuantumFunctionalEstimation.Master.Supplement
