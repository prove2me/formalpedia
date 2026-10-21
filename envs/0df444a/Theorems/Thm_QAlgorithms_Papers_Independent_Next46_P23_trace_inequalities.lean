-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_trace_inequalities
-- name    : QAlgorithms.Papers.Independent.Next46.P23.trace_inequalities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:46:44.513138+00:00
-- url     : https://prove2.me/theorems/33f3cfd3-3908-4bdd-9014-391a6dcde3bc
-- title:
--   Theorem 2.1
-- statement:
--   On a nonzero finite-dimensional complex Hilbert space, use natural logarithms, the unnormalized trace, and Schatten norms. For self-adjoint $A,B$, $$\log\frac{\operatorname{tr}(e^Ae^B)}{\operatorname{tr}(e^B)}\ge\frac{\operatorname{tr}(Ae^B)}{\operatorname{tr}(e^B)}.$$ For arbitrary positive $A,B$, Klein’s extended divergence is at least $\operatorname{tr}(A-B)$, with equality exactly when $A=B$. It is $+\infty$ if the support inclusion fails. For arbitrary matrices and conjugate exponents $p,q\in[1,\infty]$, $\|AB\|_1\le\|A\|_p\|B\|_q$; for every such $p$, $\|A+B\|_p\le\|A\|_p+\|B\|_p$. These are the four basic trace inequalities.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 35, Theorem 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Theorem2.1, all four trace inequalities, source PDF p.35.
Klein's quantity is extended at failed support inclusion; no normalization is assumed. -/
theorem trace_inequalities [Nonempty I] :
    (∀ A B : Mat I, A.IsHermitian → B.IsHermitian →
      ev (NormedSpace.exp B) A / (NormedSpace.exp B).trace.re ≤
        Real.log ((NormedSpace.exp A * NormedSpace.exp B).trace.re /
          (NormedSpace.exp B).trace.re)) ∧
    (∀ A B : Mat I, A.PosSemidef → B.PosSemidef →
      ((A - B).trace.re : EReal) ≤ kleinDivergence A B ∧
        (kleinDivergence A B = ((A - B).trace.re : EReal) ↔ A = B)) ∧
    (∀ A B : Mat I, ∀ p q : ℝ≥0∞, 1 ≤ p → 1 ≤ q → p⁻¹ + q⁻¹ = 1 →
      schattenNorm 1 (A * B) ≤ schattenNorm p A * schattenNorm q B) ∧
    (∀ A B : Mat I, ∀ p : ℝ≥0∞, 1 ≤ p →
      schattenNorm p (A + B) ≤ schattenNorm p A + schattenNorm p B) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
