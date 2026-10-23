-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_rectangleMinorants
-- name    : QAlgorithms.Papers.Independent.Information100.P08.rectangleMinorants
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:19:12.834753+00:00
-- url     : https://prove2.me/theorems/aa4d7af4-574d-4f61-9e0e-df40d4d303c7
-- title:
--   Appendix D.2: analytic rectangle minorants
-- statement:
--   Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\alpha=0.4287673$, $\beta=0.7391729$, $c_\star=1/\sqrt2-3/20$, $c(t)=9/200+(t-1/10)^2/4$, and $F(t,u)=H(u/2+c(t))-H(c_\star^2u)-\alpha-\beta(t-1/2)$. For a rectangle $[t_-,t_+]\times[u_-,u_+]\subseteq[0,1]\times[0,1/4]$ with ordered endpoints, let $c_-$ and $c_+$ be the minimum and maximum of $c$ on its first interval. At every physical point of the rectangle, $$F(t,u)\ge H(u_-/2+c_-)-H(c_\star^2u_+)-\alpha-\beta(t_+-1/2).$$ This does not require differentiability at $u=0$. If $u_->0$ and $u_+/2+c_+<1/4$, the derivatives throughout the rectangle are $F_t=(t-1/10)H\prime(u/2+c(t))/2-\beta$ and $F_u=H\prime(u/2+c(t))/2-c_\star^2H\prime(c_\star^2u)$, where $H\prime(v)=2\operatorname{atanh}(\sqrt{1-4v})/(\sqrt{1-4v}\ln2)$. For any nonnegative bounds $G_t,G_u$ on their absolute values throughout the rectangle, with midpoint $(t_0,u_0)$, $$F(t,u)\ge F(t_0,u_0)-G_t(t_+-t_-)/2-G_u(u_+-u_-)/2.$$ The guards cover the entire rectangle rather than a sampled midpoint.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 70, Appendix D.2: analytic rectangle minorants

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.69-70, (D.5)-(D.8): boundary-safe monotone minorant and whole-rectangle
mean-value bound, with differentiability guards on the entire rectangle. -/
theorem rectangleMinorants (tl th ul uh : ℝ)
    (ht : 0 ≤ tl ∧ tl ≤ th ∧ th ≤ 1) (hu : 0 ≤ ul ∧ ul ≤ uh ∧ uh ≤ 1 / 4) :
    let cm := rectangleC (max tl (min (1 / 10) th))
    let cp := max (rectangleC tl) (rectangleC th)
    (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh, u ≤ t * (1 - t) →
      determinantEntropy (ul / 2 + cm) - determinantEntropy (certificateC ^ 2 * uh) -
        certificateAlpha - certificateBeta * (th - 1 / 2) ≤ certificateResidual t u) ∧
    ((0 < ul ∧ uh / 2 + cp < 1 / 4) →
      (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
        deriv (fun x => certificateResidual x u) t =
          (t - 1 / 10) / 2 * determinantEntropyDerivative (u / 2 + rectangleC t) - certificateBeta ∧
        deriv (fun x => certificateResidual t x) u =
          determinantEntropyDerivative (u / 2 + rectangleC t) / 2 -
            certificateC ^ 2 * determinantEntropyDerivative (certificateC ^ 2 * u)) ∧
      (∀ Gt Gu : ℝ, 0 ≤ Gt → 0 ≤ Gu →
        (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          |deriv (fun x => certificateResidual x u) t| ≤ Gt) →
        (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          |deriv (fun x => certificateResidual t x) u| ≤ Gu) →
        ∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          certificateResidual ((tl + th) / 2) ((ul + uh) / 2) -
            Gt * (th - tl) / 2 - Gu * (uh - ul) / 2 ≤ certificateResidual t u)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
