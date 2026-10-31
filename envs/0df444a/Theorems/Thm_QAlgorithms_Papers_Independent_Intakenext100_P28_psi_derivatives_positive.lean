-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_psi_derivatives_positive
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.psi_derivatives_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:42:46.882629+00:00
-- url     : https://prove2.me/theorems/8c8fd5bf-9446-4c5b-93cc-9aaa2dda7548
-- title:
--   Lemma 4: psi_prime(z)+z psi_second(z)>0 for all z>0
-- statement:
--   For the smooth extension $\psi(t)=\ln t/(t-1)$, $\psi(1)=1$, and every $z>0$,
--
--   $$\psi'(z)+z\psi''(z)>0.$$
--
--   At $z=1$, the derivatives are $-1/2$ and $2/3$, giving $1/6$. The genuine derivative of the continuous extension is used.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 76, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Lemma 4: psi_prime(z)+z psi_second(z)>0 for all z>0. Sason--Verdu, arXiv:1508.00335v7, PDF p.76.  -/
theorem psi_derivatives_positive
    (z : ℝ) (hz : 0 < z) : 0 < deriv scalarLogSecant z + z * deriv (deriv scalarLogSecant) z := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
