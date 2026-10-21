-- Prove2me | Theorems.Thm_RegOTQuant_TwiceDiff_taylor_martingale_3_5
-- name    : RegOTQuant.TwiceDiff.taylor_martingale_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:04.281778+00:00
-- url     : https://prove2.me/theorems/85043296-3a01-418b-922f-73acbbe6c25b
-- title:
--   Display (3.5), p. 15 — Taylor cost bound for a martingale coupling
-- statement:
--   Let $Y$ be a closed convex subset of the Euclidean product space, let $c$ be twice continuously differentiable near $Y$ with quadratic growth, and suppose $|D^2c(x)[w,w]|\le B\|w\|^2$ for $x\in Y$, all ambient directions $w$, and $B\ge0$. Let $\nu\in\mathcal P^n(Y)$, let $\eta$ be a probability on $Y$ with finite second moment, and let $\theta$ couple $\nu$ to $\eta$ as a martingale with finite quadratic transport cost. Then
--
--   $$
--   \left|\int c\,d\eta-\int c\,d\nu\right|\le B\int\|x-y\|^2\,\theta(dx,dy).
--   $$
--
--   This is the cost estimate applied to both the original quantization coupling and the restored-marginal coupling in the proof of Theorem 3.8. The equality with $BW_2(\nu,\eta)^2$ in display (3.5) additionally uses optimality of the chosen coupling.
-- source:
--   Eckstein & Nutz, Convergence rates for regularized optimal transport via quantization, arXiv:2208.14391v3, p. 15, proof of Theorem 3.8, display (3.5)

import Mathlib
import Definitions.Def_RegOTQuant_TwiceDiff_Setting

open MeasureTheory Set

namespace RegOTQuant.TwiceDiff

/-- Display (3.5), p. 15: the Taylor cost bound for a martingale coupling.
The last equality with W₂ in the display requires the optimal coupling of Lemma 3.9. -/
theorem taylor_martingale_3_5 {N : ℕ} {d : Fin N → ℕ}
    (Y : Set (E d)) (c : E d → ℝ) (B K : ℝ)
    (hYclosed : IsClosed Y) (hYconvex : Convex ℝ Y)
    (hC2 : ∃ U : Set (E d), IsOpen U ∧ Y ⊆ U ∧ ContDiffOn ℝ 2 c U)
    (hB : 0 ≤ B) (hH : ∀ x ∈ Y, ∀ w : E d,
      |iteratedFDeriv ℝ 2 c x ![w, w]| ≤ B * ‖w‖ ^ 2)
    (hK : 0 ≤ K) (hgrowth : ∃ xhat ∈ Y,
      ∀ x ∈ Y, |c x| ≤ K * (1 + ‖x - xhat‖ ^ 2))
    (n : ℕ) (ν η : Measure (E d)) (θ : Measure (E d × E d))
    (hν : IsAtMostN n Y ν) (hη : IsP2 η ∧ η Yᶜ = 0)
    (hθprob : IsProbabilityMeasure θ)
    (hθfst : θ.map Prod.fst = ν) (hθsnd : θ.map Prod.snd = η)
    (hθmart : IsMartingaleCpl θ)
    (hθfin : (∫⁻ z : E d × E d,
      ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂θ) < ⊤) :
    |(∫ x, c x ∂η) - (∫ x, c x ∂ν)| ≤
      B * ∫ z : E d × E d, ‖z.1 - z.2‖ ^ 2 ∂θ := by sorry

end RegOTQuant.TwiceDiff
