-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_theorem_2_6
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.theorem_2_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:43:22.132968+00:00
-- url     : https://prove2.me/theorems/51efed37-586c-4261-bef6-6b33e61181b8
-- title:
--   Theorem 2.6
-- statement:
--   Let finite nonzero measures $P_t$, measurable real observables $X_t$, and positive weights $w_t\to\infty$ satisfy LD on $[a,b]$, where $a<0<b$. The index set is any unbounded subset of the positive reals, and the spaces may vary with the index. Suppose the finite continuous limiting log moment function $e$ is differentiable on $(a,b)$ and write $\phi(\theta)=\sup_{s\in[a,b]}(s\theta-e(s))$. For every open set $J\subset(D_+e(a),D_-e(b))$,
--
--   $$\lim_{t\to\infty}w_t^{-1}\log P_t(w_t^{-1}X_t\in J)=-\inf_{\theta\in J}\phi(\theta).$$
--
--   This is a local large deviation principle. For the empty open set both sides are $-\infty$, with $\inf\varnothing=+\infty$.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 9, Theorem 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2.6, local LDP including the empty open set,
arXiv:1109.3804v2, PDF pp.9--10. -/
theorem theorem_2_6 (F : LDFamily) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (e : ℝ → ℝ) (hLD : HasLD F a b e)
    (hdiff : DifferentiableOn ℝ e (Set.Ioo a b))
    (J : Set ℝ) (hJ : IsOpen J)
    (hJrange : ∀ theta ∈ J,
      rightSlope b e a < (theta : EReal) ∧ (theta : EReal) < leftSlope a e b) :
    Tendsto (scaledEvent F (fun t => {x |
      (F.weight t)⁻¹ * (F.experiment t).observable x ∈ J})) (indexFilter F)
      (nhds (-sInf ((fun theta => (legendre a b e theta : EReal)) '' J))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
