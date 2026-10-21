-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_2_5
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_2_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:42:41.356988+00:00
-- url     : https://prove2.me/theorems/79ca61db-2549-46ab-8b7a-b0a6232522f5
-- title:
--   Proposition 2.5
-- statement:
--   For finite nonzero measures $P_t$, measurable real $X_t$, and positive diverging weights $w_t$ along an unbounded positive real index set, assume LD on a nondegenerate finite interval $[a,b]$. Thus the limiting scaled log moment function $e$ is finite and continuous on that interval. Suppose that $e$ is differentiable on $(a,b)$ and put $\phi(\theta)=\sup_{s\in[a,b]}(s\theta-e(s))$. For $D_+e(a)<\theta<D_-e(b)$,
--
--   $$\liminf_{t\to\infty}w_t^{-1}\log P_t(X_t>\theta w_t)\ge-\phi(\theta).$$
--
--   This is the strict upper-tail lower bound. Zero need not lie in $(a,b)$.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 8, Proposition 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2.5, arXiv:1109.3804v2, PDF pp.8--9, (2.7).
The source does not require zero to lie in (a,b). -/
theorem proposition_2_5 (F : LDFamily) (a b : ℝ) (hab : a < b)
    (e : ℝ → ℝ) (hLD : HasLD F a b e)
    (hdiff : DifferentiableOn ℝ e (Set.Ioo a b)) (theta : ℝ)
    (htheta : rightSlope b e a < (theta : EReal) ∧ (theta : EReal) < leftSlope a e b) :
    ((-legendre a b e theta : ℝ) : EReal) ≤
      Filter.liminf (scaledEvent F (upperTail F theta)) (indexFilter F) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
