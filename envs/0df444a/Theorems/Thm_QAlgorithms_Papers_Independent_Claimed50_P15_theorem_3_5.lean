-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_theorem_3_5
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.theorem_3_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:46:24.143748+00:00
-- url     : https://prove2.me/theorems/b75d148f-c659-4324-98c1-cfb1a983d5ff
-- title:
--   Theorem 3.5
-- statement:
--   Let $(\nu_n,\omega_n)$ be faithful normalized states on possibly varying nonzero finite-dimensional systems, with positive weights $w_n\to\infty$, satisfying AF1. Thus their finite scaled Petz log-overlap limit $e$ is continuous on $[0,1]$, differentiable on $(0,1)$, and has strictly ordered endpoint slopes. For each real $r$, take the infima of the lower, upper and existing-limit type-I exponents over projection-test families $T_n$ subject to the strict constraint $\limsup_nw_n^{-1}\log\nu_n(T_n)<-r$; denote them $B_-(r),B_+(r),B(r)$. Then
--
--   $$B_-(r)=B_+(r)=B(r)=-\sup_{0\le s<1}\frac{-sr-e(s)}{1-s}\qquad(r\in\mathbb R).$$
--
--   The existing-limit infimum requires an actual extended-real limit. The equality does not assert attainment under the strict constraint.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 15, Theorem 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3.5 (Hoeffding), all real r and all three distinct infima,
arXiv:1109.3804v2, PDF p.15. No strict-constraint attainment is asserted. -/
theorem theorem_3_5 (F : FiniteTestingFamily) (hnorm : IsStateFamily F)
    (e : ℝ → ℝ) (hAF1 : HasAF1 F e) :
    ∀ r : ℝ, hoeffdingExponent F false .lower r = hoeffdingTransform e r ∧
      hoeffdingExponent F false .upper r = hoeffdingTransform e r ∧
      hoeffdingExponent F false .limit r = hoeffdingTransform e r := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
