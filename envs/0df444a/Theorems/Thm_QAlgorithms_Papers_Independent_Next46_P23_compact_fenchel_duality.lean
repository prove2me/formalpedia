-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_compact_fenchel_duality
-- name    : QAlgorithms.Papers.Independent.Next46.P23.compact_fenchel_duality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:05:37.631198+00:00
-- url     : https://prove2.me/theorems/bd15a3d0-ca96-4ad9-bf44-d69b88093ee8
-- title:
--   Theorem A.1
-- statement:
--   Let $a<b$, let $e$ be continuous and convex on $[a,b]$ and extend it by $+\infty$ elsewhere. Put $\varphi(\theta)=\sup_{s\in[a,b]}(\theta s-e(s))$. Then $$\theta s\le e(s)+\varphi(\theta),\quad\theta s=e(s)+\varphi(\theta)\iff\theta\in\partial e(s),\quad e(s)=\sup_\theta(\theta s-\varphi(\theta)),\quad\theta\in\partial e(s)\iff s\in\partial\varphi(\theta).$$ If $a<0<b$, $\varphi$ is nonincreasing up to $D_-e(0)$ and nondecreasing from $D_+e(0)$, equals $-e(0)$ on $\partial e(0)$ and is strictly greater elsewhere. Extended endpoint slopes are retained. These are precisely the five clauses.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 155, Theorem A.1

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

/-- TheoremA.1, exactly five clauses, source PDF p.155; slopes may be extended real. -/
theorem compact_fenchel_duality (a b : ℝ) (hab : a < b) (e : ℝ → ℝ)
    (hcont : ContinuousOn e (Set.Icc a b)) (hconv : ConvexOn ℝ (Set.Icc a b) e) :
    (∀ s theta : ℝ, ((theta*s : ℝ) : EReal) ≤
      compactExtension a b e s + (legendre a b e theta : EReal)) ∧
    (∀ s theta : ℝ, (((theta*s : ℝ) : EReal) =
      compactExtension a b e s + (legendre a b e theta : EReal)) ↔ subgradient a b e s theta) ∧
    (∀ s : ℝ, compactExtension a b e s =
      sSup {v | ∃ theta : ℝ, v = ((theta*s-legendre a b e theta : ℝ) : EReal)}) ∧
    (∀ s theta : ℝ, subgradient a b e s theta ↔ dualSubgradient (legendre a b e) theta s) ∧
    (a < 0 ∧ 0 < b →
      AntitoneOn (legendre a b e) {theta | (theta : EReal) ≤ leftSlope a e 0} ∧
      MonotoneOn (legendre a b e) {theta | rightSlope b e 0 ≤ (theta : EReal)} ∧
      (∀ theta : ℝ, subgradient a b e 0 theta → legendre a b e theta = -e 0) ∧
      (∀ theta : ℝ, ¬subgradient a b e 0 theta → -e 0 < legendre a b e theta)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
