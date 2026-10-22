-- Prove2me | Theorems.Thm_PostTruth_Regimes_threshold_gap
-- name    : PostTruth.Regimes.threshold_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:34.038441+00:00
-- url     : https://prove2.me/theorems/7f47f0b7-44f1-4bfa-be21-8448bd4bd794
-- title:
--   Proof of Theorem 1 — the difference between Bayesian and DeGroot cutoffs
-- statement:
--   For $1/2<p\leq1$ and $0<q<1/2$, let $d=(2p-1)(1-q)/q$ be the two-narrative gap and let $\widetilde r_L=(1-2(1-q)(1-p))/(2q)$ be the DeGroot cutoff when the true state is $L$. Then
--
--   $$
--   d-\widetilde r_L=\frac{2p(1-q)-1}{2q},
--   \qquad
--   d-\widetilde r_L=0\iff q=q^*=\frac{2p-1}{2p},
--   \qquad
--   d-\widetilde r_L<0\iff q>q^*.
--   $$
--
--   The right-hand expression is strictly decreasing as a function of positive $q$. This identity locates the change in the ordering of the two societies' mislearning cutoffs.
-- source:
--   Mostagir & Siderius, Learning in a Post-Truth World, SSRN working paper 3879174 (version of 2 July 2021), p. 20, proof of Theorem 1 (displayed cutoff difference); https://ssrn.com/abstract=3879174

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model

namespace PostTruth.Regimes

/-- The displayed cutoff difference in the proof of Theorem 1, p. 20. -/
theorem threshold_gap (p q : ℝ) (hpq : Standing p q) :
    gap p q - rTilde p q = (2 * p * (1 - q) - 1) / (2 * q) ∧
    (gap p q - rTilde p q = 0 ↔ q = qStar p) ∧
    (gap p q - rTilde p q < 0 ↔ qStar p < q) ∧
    StrictAntiOn (fun t : ℝ => (2 * p * (1 - t) - 1) / (2 * t))
      (Set.Ioi 0) := by sorry

end PostTruth.Regimes
