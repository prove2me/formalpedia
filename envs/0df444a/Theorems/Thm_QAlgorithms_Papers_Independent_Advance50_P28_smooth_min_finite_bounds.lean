-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_smooth_min_finite_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.smooth_min_finite_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:47:05.88444+00:00
-- url     : https://prove2.me/theorems/e405f954-d0ba-483d-8a0e-eeca22a510f1
-- title:
--   Smooth min-entropy finite bound (30)–(35)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. Fix an independent universal2 ensemble and set $\overline d=\mathbb E_Xd_1(f_{X*}P,U_M)$, $g(s)=-\log\sum_aP(a)^{1+s}$, $g(0)=0$. For every subdistribution $Q$, every $u\ge\log M$, and every $s\ge0$,
--   $$\begin{aligned}\overline d&\le\sqrt{M\max_aP(a)},\\\overline d&\le\sqrt{M\max_aQ(a)}+2\|P-Q\|_1,\\\overline d&\le\sqrt{Me^{-u}}+2P\{P(a)>e^{-u}\},\\\overline d&\le3\exp\!\left(-\frac{g(s)-s\log M}{1+2s}\right).\end{aligned}$$
--   The last bound also holds after taking the infimum of its right side over $s\ge0$. These are the finite smoothing comparisons, without claiming a finite optimizer in the unbounded parameter.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 7, Smooth min-entropy finite bound (30)–(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.6–7, (30)–(35): finite min-entropy, threshold and optimized
renyiPowerSum bounds, using an infimum over the unbounded real parameter. -/
theorem smooth_min_finite_bounds {A : Type*} [Fintype A] [Nonempty A]
    {M : ℕ} (hM : 0 < M) (h : HashEnsemble A M) (hu : Universal2 h)
    (P : A → ℝ) (hP : IsLaw P) :
    expectedError h P ≤ Real.sqrt ((M : ℝ) * peak P) ∧
    (∀ Q : A → ℝ, IsSubLaw Q → expectedError h P ≤
      Real.sqrt ((M : ℝ) * peak Q) + 2 * l1 P Q) ∧
    (∀ threshold : ℝ, Real.log (M : ℝ) ≤ threshold → expectedError h P ≤
      Real.sqrt ((M : ℝ) * Real.exp (-threshold)) +
        2 * ∑ a, if Real.exp (-threshold) < P a then P a else 0) ∧
    (∀ s : ℝ, 0 ≤ s → expectedError h P ≤
      3 * Real.exp (-(renyiNumerator P s - s * Real.log (M : ℝ)) / (1 + 2 * s))) ∧
    expectedError h P ≤ sInf ((fun s : ℝ =>
      3 * Real.exp (-(renyiNumerator P s - s * Real.log (M : ℝ)) / (1 + 2 * s))) '' Set.Ici 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
