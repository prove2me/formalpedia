-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_pureLoss_jumpTimes
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.pureLoss_jumpTimes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:37:26.674486+00:00
-- url     : https://prove2.me/theorems/99eb8f23-5d77-439e-bdaf-f85a9570bcf7
-- title:
--   Pure-loss jump times change only a scalar at fixed count
-- statement:
--   Let $\kappa,t>0$, let $\ell\ge0$ be an integer, and let $0\le\tau_1\le\cdots\le\tau_\ell\le t$. Put $\gamma=1-e^{-\kappa t}$. Form the chronological trajectory operator by alternating no-jump factors $e^{-\kappa s\hat n/2}$ over successive intervals with $\ell$ annihilations, followed by the final no-jump interval. As in (8.3), omit scalar jump-rate factors. Its number-basis formula has a bounded extension to every oscillator Hilbert vector, and
--
--   $$\widetilde E_\ell=f_\ell E_\ell,\qquad f_\ell=\frac{\sqrt{\ell!}\,e^{-\kappa\sum_j\tau_j/2}}{\gamma^{\ell/2}}>0.$$
--
--   The output is square summable for every square-summable input. No zero-probability branch is normalized. Thus jump times provide only a scalar at fixed loss count. Obtaining the count by parity monitoring separately presupposes fixed initial parity and ideal arbitrarily fast QND parity measurements.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 22, §VIII B (8.3)–(8.4): pure-loss jump times carry no extra recovery information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.22 (8.3)--(8.4): jump-time dependence is a positive scalar for a fixed
lost-photon count. The domain clause excludes renormalization of zero branches.
Parity tracking additionally needs fixed input parity and ideal fast QND measurements;
this operator identity itself is valid on arbitrary physical input vectors. -/
theorem pureLoss_jumpTimes (k t : ℝ) (hk : 0 < k) (ht : 0 < t) (l : ℕ)
    (times : Fin l → ℝ) (hord : Monotone times)
    (hrange : ∀ i, 0 ≤ times i ∧ times i ≤ t) :
    let g := 1 - Real.exp (-k * t)
    0 < trajectoryScalar k times g ∧
    (∀ v : FockCoordinates, fockDomain v →
      fockDomain (jumpTrajectory k t times v) ∧
      jumpTrajectory k t times v = (trajectoryScalar k times g : ℂ) • lossVector g l v) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
