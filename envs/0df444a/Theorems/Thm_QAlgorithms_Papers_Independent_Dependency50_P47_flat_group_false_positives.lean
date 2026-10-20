-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_flat_group_false_positives
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.flat_group_false_positives
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:45:49.772268+00:00
-- url     : https://prove2.me/theorems/78620d5e-a001-41b9-82f4-a87db1bb50b3
-- title:
--   Lemma 5: false-positive bound for a group of flat typical states
-- statement:
--   Let $P,P_y$ be orthogonal projectors on one finite-dimensional register, and let $0<\epsilon<1$, $\alpha,\delta,c>0$, $\delta''\ge0$, and $h_F,h_{F|Y}\in\mathbb R$ satisfy the preceding rank estimates
--
--   $$
--   \operatorname{tr}P\ge(1-\epsilon)2^{n(h_F-c\delta)},\qquad
--   \operatorname{tr}P_y\le2^{n(h_{F|Y}+\delta'')}.
--   $$
--
--   For any natural number $m\le2^{n(h_F-h_{F|Y}-\delta''-c\delta-\alpha)}$, apply $\{P_y,I-P_y\}$ independently to $m$ copies of $\tau=P/\operatorname{tr}P$, before conditioning on Alice's selected success. If $N$ is the number of accepting outcomes, then
--
--   $$
--   \Pr\{N>1\}\le\frac{2^{-\alpha n+1}}{1-\epsilon}.
--   $$
--
--   Equivalently, for $t=\operatorname{tr}(P_y\tau)$ the probability is $1-(1-t)^m-mt(1-t)^{m-1}$, with the $m=0$ last term equal to zero. In the typical-subspace application $h_F=H(F)$ and $h_{F|Y}=H(F\mid Y)$. The formulation handles integer rounding and does not assume the proof's unnecessary small-$t$ estimate.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 22, Lemma 5: false-positive bound for a group of flat typical states

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Lemma 5, PDF pp.17,22,24: finite-block rank formulation of the false-positive bound.
The m copies are the independent flat typical state before conditioning on Alice's success.
Any integer m below the displayed real group size is permitted, including zero. -/
theorem flat_group_false_positives {D : Type} [Fintype D] [DecidableEq D]
    (P Py : Matrix D D ℂ) (hP : IsProjection P) (hPy : IsProjection Py)
    (n m : ℕ) (eps alpha delta dd c hF hFY : ℝ)
    (heps0 : 0 < eps) (heps1 : eps < 1) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hdd : 0 ≤ dd) (hc : 0 < c)
    (hrankP : (1 - eps) * (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta)) ≤ P.trace.re)
    (hrankY : Py.trace.re ≤ (2 : ℝ) ^ ((n : ℝ) * (hFY + dd)))
    (hgroup : (m : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (hF - hFY - dd - c * delta - alpha))) :
    moreThanOneProbability m (effectProb Py (normalize P)) ≤
      (2 : ℝ) ^ (-alpha * n + 1) / (1 - eps) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
