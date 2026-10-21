-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_log_schatten_convex
-- name    : QAlgorithms.Papers.Independent.Next46.P23.log_schatten_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:50:30.990324+00:00
-- url     : https://prove2.me/theorems/c6f736e6-f795-41cf-8c2a-668c49972d78
-- title:
--   Corollary 2.4
-- statement:
--   For positive matrices $A,B$ on a nonzero finite-dimensional complex Hilbert space and finite $p\ge1$, set $f(\alpha)=\log\|A^\alpha B^{1-\alpha}\|_p^p$. Powers are zero on each kernel, also at exponent zero, and $\log0=-\infty$. Then, for real $a,b$ and $0\le u\le1$, $$f(ua+(1-u)b)\le uf(a)+(1-u)f(b).$$ This extended convexity includes the identically $-\infty$ case of orthogonal supports.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 39, Corollary 2.4

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

/-- Corollary2.4, extended convexity including orthogonal supports, source PDF p.39. -/
theorem log_schatten_convex [Nonempty I] (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℝ) (hp : 1 ≤ p) :
    let F : ℝ → EReal := fun a => ENNReal.log (ENNReal.ofReal
      ((schattenNorm (ENNReal.ofReal p) (supportPower A a * supportPower B (1-a))) ^ p))
    ∀ a b u : ℝ, 0 ≤ u → u ≤ 1 →
      F (u*a + (1-u)*b) ≤ (u : EReal) * F a + ((1-u : ℝ) : EReal) * F b := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
