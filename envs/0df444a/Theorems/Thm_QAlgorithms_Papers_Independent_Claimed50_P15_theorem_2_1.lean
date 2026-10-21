-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_theorem_2_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.theorem_2_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:39:35.78299+00:00
-- url     : https://prove2.me/theorems/9c06c230-cd13-4ccd-b598-58ca3e4227b9
-- title:
--   Theorem 2.1
-- statement:
--   Let $a<b$ be real and let $e:[a,b]\to\mathbb R$ be continuous and convex, extended by $+\infty$ outside $[a,b]$. Write $\phi(\theta)=\sup_{s\in[a,b]}(s\theta-e(s))$, $\partial$ for the supporting-line subdifferential, and $D_\pm$ for the extended one-sided slopes. Then, for all real $s,\theta$,
--
--   $$s\theta\le e(s)+\phi(\theta),\qquad s\theta=e(s)+\phi(\theta)\iff\theta\in\partial e(s)\iff s\in\partial\phi(\theta),\qquad e(s)=\sup_{\theta\in\mathbb R}(s\theta-\phi(\theta)).$$
--
--   If $a<0<b$, the function $\phi$ is nonincreasing on $(-\infty,D_-e(0)]$, nondecreasing on $[D_+e(0),\infty)$, equals $-e(0)$ on $\partial e(0)$, and is strictly greater elsewhere. Finally, $\phi(\theta)=a\theta-e(a)$ when $\theta\le D_+e(a)$, and $\phi(\theta)=b\theta-e(b)$ when $\theta\ge D_-e(b)$.
--
--   These are the six duality and endpoint properties used in the deviation bounds.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 6, Theorem 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2.1, all six clauses, arXiv:1109.3804v2, PDF pp.6--7.
Outside [a,b], e is positive infinity. Monotonicity is nonstrict. -/
theorem theorem_2_1 (a b : ℝ) (hab : a < b) (e : ℝ → ℝ)
    (hcont : ContinuousOn e (Set.Icc a b)) (hconv : ConvexOn ℝ (Set.Icc a b) e) :
    (∀ s theta : ℝ, ((s * theta : ℝ) : EReal) ≤
      extendedConvex a b e s + (legendre a b e theta : EReal)) ∧
    (∀ s theta : ℝ, (((s * theta : ℝ) : EReal) =
      extendedConvex a b e s + (legendre a b e theta : EReal)) ↔
      convexSubgradient a b e s theta) ∧
    (∀ s theta : ℝ, convexSubgradient a b e s theta ↔
      finiteSubgradient (legendre a b e) theta s) ∧
    (∀ s : ℝ, extendedConvex a b e s =
      sSup {v | ∃ theta : ℝ, v = ((s * theta - legendre a b e theta : ℝ) : EReal)}) ∧
    (a < 0 ∧ 0 < b →
      AntitoneOn (legendre a b e) {theta | (theta : EReal) ≤ leftSlope a e 0} ∧
      MonotoneOn (legendre a b e) {theta | rightSlope b e 0 ≤ (theta : EReal)} ∧
      (∀ theta : ℝ, convexSubgradient a b e 0 theta → legendre a b e theta = -e 0) ∧
      (∀ theta : ℝ, ¬convexSubgradient a b e 0 theta → -e 0 < legendre a b e theta)) ∧
    ((∀ theta : ℝ, (theta : EReal) ≤ rightSlope b e a → legendre a b e theta = a * theta - e a) ∧
      (∀ theta : ℝ, leftSlope a e b ≤ (theta : EReal) → legendre a b e theta = b * theta - e b)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
