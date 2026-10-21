-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_strict_tail_lower_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P23.strict_tail_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:06:19.962402+00:00
-- url     : https://prove2.me/theorems/6d1e229d-6849-450f-bc1b-ae0e45ce7831
-- title:
--   Proposition A.4
-- statement:
--   Let $t$ range over an arbitrary unbounded subset of positive real numbers. Let $X_t$ be measurable on varying finite nonzero measure spaces $(M_t,P_t)$, without probability normalization. Suppose the normalized log-moments converge to a finite continuous $e$ on $[a,b]$, where $a<0<b$, and $e$ is differentiable on $(a,b)$. With the compact-domain Fenchel transform $\varphi$, for $D_+e(a)<\theta<D_-e(b)$, $$\liminf_{t\to\infty}\frac1t\log P_t\{X_t>t\theta\}\ge-\varphi(\theta).$$ Logarithms of zero masses are $-\infty$, and the tail is strict.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 157, Proposition A.4

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

/-- PropositionA.4, strict upper-tail lower bound, source PDF p.157.
Times are real, masses need not be one, and a<0<b is retained. -/
theorem strict_tail_lower_bound (F : ScalarLD) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (e : ℝ → ℝ) (hLD : ScalarHasLD F a b e) (hdiff : DifferentiableOn ℝ e (Set.Ioo a b))
    (theta : ℝ) (htheta : rightSlope b e a < (theta : EReal) ∧ (theta : EReal) < leftSlope a e b) :
    ((-legendre a b e theta : ℝ) : EReal) ≤
      Filter.liminf (upperTailLog F theta) (timeFilter F) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
