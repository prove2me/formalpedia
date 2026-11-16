-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_rank_transfer
-- name    : QuantumFunctionalEstimation.Master.Supplement.rank_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:49.976138+00:00
-- url     : https://prove2.me/theorems/a22ff6e7-3c59-4c89-a8dc-ce08da974c74
-- title:
--   Lemma 5.21 — rank-testing transfer
-- statement:
--   There are universal $C,c,k>0$ and $d_0\ge2$ such that the following holds for every $d\ge d_0$. Set $q=\lfloor d/4\rfloor$. Let $\nu_0,\nu_1$ be $K$-matching laws supported on $\{0\}\cup[\ell,b_0]$, with common mean at most one and $0<\ell\le1/2$. Put $\pi_b=\Pr_{\nu_b}(X>0)$, $\gamma=\pi_1-\pi_0\ge1/4$ and $M=\max\{1,b_0-1\}$. Assume $K\ge C\log d$ and $(1+M)^2\log d\le cd$. For every integer $r_0$ in the entire interval
--   $$d-q+\pi_0q+\gamma q/4+1\le r_0\le d-q+\pi_1q-\gamma q/4+1,$$
--   and every $0<p\le1/2$, every two-sided collective tester in dimension $d+1$ distinguishing rank at most $r_0$ from $\Delta_{r_0}\ge cp\ell$ with success at least $2/3$ requires
--   $$N\ge k\frac{d^2}{pM^2}.$$
--   This is the rank-testing transfer; the same constant $c$ occurs in the parameter constraint and distance promise.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: asymptotic lower bounds for large dimension or rank and small positive error → positive multipliers and independent integer and error thresholds before varying parameters, with the complete displayed rates; reason: expands Omega uniformly without choosing numeric lower-bound multipliers or dropping regimes
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 34 (PDF p. 36), Lemma 5.21

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.21, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem rank_transfer :
  ∃ C c k : ℝ, 0 < C ∧ 0 < c ∧ 0 < k ∧
  ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ K : ℕ,
  ∀ μ₀ μ₁ : ProbabilityMeasure ℝ, ∀ ℓ b : ℝ,
    0 < ℓ → ℓ ≤ 1 / 2 → MomentMatching K μ₀ μ₁ →
    Supported μ₀ ({0} ∪ Set.Icc ℓ b) → Supported μ₁ ({0} ∪ Set.Icc ℓ b) →
    mean μ₀ = mean μ₁ → mean μ₀ ≤ 1 →
    let q : ℕ := d / 4
    let π₀ := positiveMass μ₀
    let π₁ := positiveMass μ₁
    let γ := π₁ - π₀
    let M := max 1 (b - 1)
    1 / 4 ≤ γ → C * Real.log d ≤ K → (1 + M)^2 * Real.log d ≤ c * d →
    ∀ r : ℕ, (d : ℝ) - q + π₀ * q + γ * q / 4 + 1 ≤ r →
      (r : ℝ) ≤ (d : ℝ) - q + π₁ * q - γ * q / 4 + 1 →
    ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ N : ℕ,
    ∀ E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin (d + 1)) Bool,
      RankSuccessful (d + 1) r N (c * p * ℓ) E → k * (d : ℝ)^2 / (p * M^2) ≤ N := by sorry

end QuantumFunctionalEstimation.Master.Supplement
