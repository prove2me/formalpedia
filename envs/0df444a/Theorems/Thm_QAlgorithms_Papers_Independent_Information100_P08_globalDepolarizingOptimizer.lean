-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_globalDepolarizingOptimizer
-- name    : QAlgorithms.Papers.Independent.Information100.P08.globalDepolarizingOptimizer
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:18:29.928987+00:00
-- url     : https://prove2.me/theorems/e849fd94-9ae6-44c3-9a56-e67c3b168068
-- title:
--   Appendix C: global depolarizing optimizer
-- statement:
--   Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Fix $0<p<2/3$, set $t=1-p$, $\kappa=1-3p/2$, $s(r)=\sqrt{1-\kappa^2+\kappa^2r^2}$, and $G(r)=h_2((1+tr)/2)-h_2((1+s(r))/2)$ for $r\in[0,1]$. Let $L(x)=\operatorname{atanh}(x)/x$ with continuous value $L(0)=1$, and $K=\kappa^2L(\sqrt{1-\kappa^2})-t^2$. If $K\ge0$, $$G(0)\le G(r)\quad(0\le r\le1).$$ If $K<0$, there is exactly one stationary point $r_\star\in(0,1)$; $G$ is strictly decreasing on $[0,r_\star]$ and strictly increasing on $[r_\star,1]$. This is the global optimizer characterization, including the sign extension at zero.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 68, Appendix C: global depolarizing optimizer

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.68-69, Appendix C: global optimizer classification, including the continuously
extended sign at zero, all stationary points, and monotonicity on both sides of the unique one. -/
theorem globalDepolarizingOptimizer (p : ℝ) (hp : 0 < p) (hpUpper : p < 2 / 3) :
    (0 ≤ optimizerSign p → ∀ r ∈ Set.Icc (0 : ℝ) 1, optimizerPenalty p 0 ≤ optimizerPenalty p r) ∧
    (optimizerSign p < 0 → ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      deriv (optimizerPenalty p) r = 0 ∧
      (∀ z ∈ Set.Ioo (0 : ℝ) 1, deriv (optimizerPenalty p) z = 0 ↔ z = r) ∧
      StrictAntiOn (optimizerPenalty p) (Set.Icc 0 r) ∧
      StrictMonoOn (optimizerPenalty p) (Set.Icc r 1)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
