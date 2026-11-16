-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_tsallis_lower_bounds
-- name    : QuantumFunctionalEstimation.Master.Supplement.tsallis_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:05:33.908212+00:00
-- url     : https://prove2.me/theorems/9c5deec2-f258-4ffd-846f-4fce584873c2
-- title:
--   Theorem 5.11 — Tsallis sample and query lower bounds, both regimes
-- statement:
--   Let $\rho$ be any unknown $d$-dimensional density matrix. Estimating $S^T_\alpha(\rho)$ to additive error $\varepsilon$ with probability at least $2/3$, uniformly on all states, requires $N\ge kR$ samples, where
--   $$R_\alpha(d,\varepsilon)=\begin{cases}\dfrac{d^{1+1/\alpha}}{\varepsilon^{1/\alpha}\log^2d\max\{1,\varepsilon^{1/\alpha}\log^2d\}}+\dfrac{d^{2-2\alpha}}{\varepsilon^2},&0<\alpha<1,\\\dfrac{\varepsilon^{-2/(\alpha-1)}}{\log^4(1/\varepsilon)},&1<\alpha<2.\end{cases}.$$
--
--   For each fixed allowed $\alpha$, choose $k>0$, $\varepsilon_0\in(0,1/2]$ and $d_0\ge2$ depending only on $\alpha$, before all $d\ge d_0$ and $0<\varepsilon\le\varepsilon_0$. In the regime $1<\alpha<2$, also choose $a_\alpha>0$ before the error and require $d\ge1+\lfloor a_\alpha\varepsilon^{-1/(\alpha-1)}\rfloor$; there is no upper bound on $d$. For every purified state-preparation query estimator, the same regime also has $Q\ge k\sqrt R$, retaining the introductory alias and its logarithmic factors. This includes every environment size $e\ge d$ and every oracle completion of each input.
--
--   This companion theorem records the complete application rate; it is not a dependency used to prove the master goal.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
--   - encoding: introductory purified-query lower bound with displayed or suppressed logarithms → query bound k times the square root of the complete sample rate, using controlled forward and adjoint calls; reason: printed p. 3 (PDF p. 5) lifts the complete sample rate; its square root supplies explicit logarithmic factors and implies the introductory tilde-Omega announcement
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 29 (PDF p. 31), Theorem 5.11; alias Theorem 1.4, printed p. 5 (PDF p. 7)

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Theorem 5.11, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem tsallis_lower_bounds :
  ∀ α : ℝ, 0 < α → α < 2 → α ≠ 1 →
  ∃ a k ε₀ : ℝ, 0 < a ∧ 0 < k ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
  ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    (1 < α → 1 + ⌊a * ε^(-1 / (α - 1))⌋₊ ≤ d) →
    EstimationBounds (@tsallis d α) ε k (tsallisRate α d ε) := by sorry

end QuantumFunctionalEstimation.Master.Supplement
