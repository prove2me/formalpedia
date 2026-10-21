-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P09_actual_resolventFacts
-- name    : QAlgorithms.Papers.Independent.Next46.P09.actual_resolventFacts
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:03:28.553956+00:00
-- url     : https://prove2.me/theorems/f8b547a2-d10e-41b7-9505-58a569ebe4c6
-- title:
--   Laplace resolvent, recovery, and full generator domain
-- statement:
--   Let $(T_t)_{t\ge0}$ be a dynamical semigroup on the full complex trace class of a separable complete complex Hilbert space $H$, with complete positivity, nonincrease of trace on positive inputs, and the trace-pairing continuity of Problem I.1. Let $L$ be its actual trace-norm right-derivative generator. For every $\lambda>0$ the Laplace integral defines a complex linear completely positive resolvent $R_\lambda$ satisfying
--
--   $$R_\lambda\rho=\int_0^\infty e^{-\lambda t}T_t\rho\,dt,\qquad\|\lambda R_\lambda\|_{1\to1}\le1.$$
--
--   For all $\lambda,\mu>0$ and $\rho\in\mathcal T(H)$,
--
--   $$R_\lambda-R_\mu=(\mu-\lambda)R_\lambda R_\mu,\qquad\operatorname{dom}L=R_\lambda\mathcal T(H),\qquad LR_\lambda\rho=\lambda R_\lambda\rho-\rho.$$
--
--   For every $t>0$ one recovers the semigroup in the strong trace-norm topology:
--
--   $$T_t\rho=\lim_{n\to\infty}(n/t)^nR_{n/t}^{\,n}\rho.$$
--
--   At $t=0$ the semigroup is the identity. This result concerns actual semigroups and makes no converse assertion for arbitrary resolvent families. The formalization characterizes the Laplace integral by all bounded trace pairings and explicitly includes integrability.
-- source:
--   Unbounded generators of dynamical semigroups, arXiv:1707.02266v1, PDF p. 7, Section II.C, actual-semigroup resolvent facts (11)–(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P09

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass IsTraceClass traceNormValue operatorTrace IsPositive)

open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Section II.C, arXiv:1707.02266v1, PDF p.7, (11)–(13).
This is only the actual-semigroup direction. The norm bound is written as its
equivalent inequality on every trace-class input. Recovery is in trace norm at
t > 0; T_0 is supplied by the semigroup identity, without division by zero. -/
theorem actual_resolventFacts [TopologicalSpace.SeparableSpace H]
    {I : Type v} (b : HilbertBasis I ℂ H) (T : TraceDynamicalSemigroup b) :
    ∃ R : ℝ → TraceClass H → TraceClass H,
      (∀ lambda : ℝ, 0 < lambda →
        IsTraceLinear (R lambda) ∧ IsTraceCP (R lambda) ∧
        IsLaplaceResolvent T lambda (R lambda) ∧
        (∀ rho : TraceClass H,
          traceNormValue ((lambda : ℂ) • (R lambda rho).val) ≤ traceNormValue rho.val) ∧
        (∀ rho : TraceClass H,
          rho ∈ TraceGeneratorDomain T ↔ ∃ sigma, R lambda sigma = rho) ∧
        (∀ rho eta : TraceClass H, InTraceGeneratorGraph T (R lambda rho) eta ↔
          eta.val = (lambda : ℂ) • (R lambda rho).val - rho.val)) ∧
      (∀ lambda mu : ℝ, 0 < lambda → 0 < mu → ∀ rho : TraceClass H,
        (R lambda rho).val - (R mu rho).val =
          ((mu - lambda : ℝ) : ℂ) • (R lambda (R mu rho)).val) ∧
      (∀ (t : ℝ), 0 < t → ∀ rho : TraceClass H,
        Tendsto (fun n : ℕ => traceNormValue
          (((n : ℂ) / (t : ℂ)) ^ n • ((R ((n : ℝ) / t))^[n] rho).val -
            (T.maps t.toNNReal rho).val)) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P09

end
