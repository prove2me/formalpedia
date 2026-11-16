-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_tsallis_transfer
-- name    : QuantumFunctionalEstimation.Master.Supplement.tsallis_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:13.119913+00:00
-- url     : https://prove2.me/theorems/8a0a1d1d-8a69-48e5-a7c0-91c19ea61717
-- title:
--   Lemma 5.10 — Tsallis entropy transfer
-- statement:
--   Fix $0<\alpha<2$, $\alpha\ne1$. Choose the positive approximation witnesses $c_\alpha,\gamma_\alpha$ of Lemma 5.4 and set $\Delta_\alpha=2c_\alpha\gamma_\alpha^\alpha$. There are $k_\alpha>0$ and $d_0\ge2$, independent of error, such that for every $d\ge d_0$ and $\varepsilon>0$, setting
--   $$h=\left(\frac{32|1-\alpha|}{\Delta_\alpha}\varepsilon d^{\alpha-1}\right)^{1/\alpha}\le\tfrac14,$$
--   every collective estimator of $S^T_\alpha$ in dimension $d+1$, uniformly successful at error $\varepsilon$ with probability at least $2/3$, requires
--   $$N\ge k_\alpha\frac{d^2}{h\log^2d\max\{1,h\log^2d\}}.$$
--   This transfer supplies the dimension/error relation in Theorem 5.11.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
--   - encoding: the fixed approximation constants from Lemma 5.4 → alpha-only existential constants satisfying PowerWitness; reason: pins the uniform Lemma 5.4 inequality and identifies Delta_alpha as 2*c_alpha*gamma_alpha^alpha
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 28 (PDF p. 30), Lemma 5.10

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.10, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem tsallis_transfer :
  ∀ α : ℝ, 0 < α → α < 2 → α ≠ 1 →
  ∃ c γ : ℝ, PowerWitness α c γ ∧
  ∃ k : ℝ, 0 < k ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε →
    let h := (32 * |1 - α| / powerGap α c γ * ε * (d : ℝ)^(α - 1))^(1 / α)
    h ≤ 1 / 4 → SampleBound (@tsallis (d + 1) α) ε (k * transitionRate d h) := by sorry

end QuantumFunctionalEstimation.Master.Supplement
