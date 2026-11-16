-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_trace_moments
-- name    : QuantumFunctionalEstimation.Master.Supplement.trace_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:42.824244+00:00
-- url     : https://prove2.me/theorems/2b436f14-fb1b-4a07-9f1c-f70748ee8177
-- title:
--   Lemma 5.13 — trace-distance moment matching
-- statement:
--   Choose the fixed positive approximation witnesses $D>1$, $c_0,c_1\in(0,1)$ of Lemma 5.12. Every integer $K\ge2$ and $K^{-2}\le a\le1/2$ admit laws $\nu_0,\nu_1$ supported on $[1/4,1/4+3/(4a)]$, matching moments through $K+1$, with common mean $1/4+3/(4D)<1$, such that for $\phi_T(x)=\max\{1-x,0\}$,
--   $$\mathbb E_{\nu_1}\phi_T(Y)-\mathbb E_{\nu_0}\phi_T(Y)\ge\frac{3c_0}{4DK\sqrt a}.$$
--   The approximation witness property is retained with the constants. This supplies the trace-distance separation for Theorem 5.14.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: the fixed approximation constants from Lemma 5.12 → existential constants satisfying both regimes of TraceWitness; reason: pins the uniform Lemma 5.12 inequalities, D>1 and c0,c1 in (0,1) before K and a
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 30 (PDF p. 32), Lemma 5.13

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.13, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem trace_moments :
  ∃ D c₀ c₁ : ℝ, TraceWitness D c₀ c₁ ∧
  ∀ K : ℕ, 2 ≤ K → ∀ a : ℝ, (K : ℝ)⁻¹ ^ 2 ≤ a → a ≤ 1 / 2 →
  ∃ μ₀ μ₁ : ProbabilityMeasure ℝ,
    MatchingOn (K + 1) (Set.Icc (1 / 4) (1 / 4 + 3 / (4 * a)))
      (1 / 4 + 3 / (4 * D)) μ₀ μ₁ ∧
    1 / 4 + 3 / (4 * D) < 1 ∧
    Integrable (fun x : ℝ => max (1 - x) 0) (μ₀ : Measure ℝ) ∧
    Integrable (fun x : ℝ => max (1 - x) 0) (μ₁ : Measure ℝ) ∧
    3 * c₀ / (4 * D * K * Real.sqrt a) ≤
      expectation (fun x => max (1 - x) 0) μ₁ - expectation (fun x => max (1 - x) 0) μ₀ := by sorry

end QuantumFunctionalEstimation.Master.Supplement
