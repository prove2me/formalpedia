-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_theorem_3_6
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.theorem_3_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:47:04.687688+00:00
-- url     : https://prove2.me/theorems/a8c9d3e9-74e0-4a04-b091-e7ab63a21c6f
-- title:
--   Theorem 3.6
-- statement:
--   Let faithful normalized finite-dimensional state pairs $(\nu_n,\omega_n)$ with positive diverging weights $w_n$ satisfy AF1 and AF2. AF1 gives a finite continuous Petz log-overlap limit $e$ on $[0,1]$, differentiable on $(0,1)$, with strictly ordered endpoint slopes. AF2 extends the finite limits to $[0,1+\delta)$ for some $\delta>0$ and requires differentiability at one. For $0<\epsilon<1$, define $B_-^\epsilon,B_+^\epsilon,B^\epsilon$ by infimizing respectively the liminf, limsup and genuine-limit type-I exponents over projection families with $\nu_n(T_n)\le\epsilon$ for every $n$. Then
--
--   $$B_-^\epsilon=B_+^\epsilon=B^\epsilon=-\Sigma^+,\qquad\Sigma^+=e'(1).$$
--
--   This is the fixed-error Stein exponent in the source's sign convention.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 16, Theorem 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3.6 (Stein), arXiv:1109.3804v2, PDF p.16.
The source uses every-index type-II constraints and Sigma+=e'(1). -/
theorem theorem_3_6 (F : FiniteTestingFamily) (hnorm : IsStateFamily F)
    (e : ℝ → ℝ) (hAF1 : HasAF1 F e) (hAF2 : HasAF2 F e) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      steinExponent F false .lower epsilon = (-deriv e 1 : ℝ) ∧
      steinExponent F false .upper epsilon = (-deriv e 1 : ℝ) ∧
      steinExponent F false .limit epsilon = (-deriv e 1 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
