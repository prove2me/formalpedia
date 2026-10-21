-- Prove2me | Theorems.Thm_RotationContagion_Rotation_loss_inflection
-- name    : RotationContagion.Rotation.loss_inflection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:33.602102+00:00
-- url     : https://prove2.me/theorems/821273fc-a867-4cc4-be3e-7a03ff0f548e
-- title:
--   §2.1, p. 7 — b is the inflexion point of ℓ: ℓ(b) = 1/2, convex below b, concave above
-- statement:
--   Let $\gamma > 0$, $K > 1$, $R \ge 0$, $b = \frac1\gamma\ln(K-1)$ and $\ell(t) = e^{\gamma(t-b)}/(1+e^{\gamma(t-b)})$. Then
--   $$\ell(b) = \tfrac12,$$
--   $\ell$ is convex on $(-\infty, b]$ and concave on $[b, \infty)$.
--
--   Thus $b$ is the time the uninterrupted diffusion takes to infect half the group, and the curvature of $\ell$ changes there. The comparison of $R/2$ with $b$ in Lemma 3 and Proposition 1 rests on this.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), p. 7, §2.1 (the summary parameter b)

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

/-- §2.1, p. 7: `b` is the inflexion point of `ℓ`: `ℓ(b) = 1/2`, `ℓ` is convex below `b` and
concave above `b`. -/
theorem loss_inflection (P : Params) (hP : P.Standing) :
    loss P (b P) = 1 / 2 ∧ ConvexOn ℝ (Set.Iic (b P)) (loss P) ∧
      ConcaveOn ℝ (Set.Ici (b P)) (loss P) := by sorry

end RotationContagion.Rotation
