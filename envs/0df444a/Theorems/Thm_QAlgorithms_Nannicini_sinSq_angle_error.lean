-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_sinSq_angle_error
-- name    : QAlgorithms.Nannicini.sinSq_angle_error
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:47:23.084782+00:00
-- url     : https://prove2.me/theorems/619ad1ef-a1ab-49d8-8d57-7f6a1baf2d4a
-- title:
--   Angle error to probability error for sin²
-- statement:
--   This lemma converts an error in an estimated angle into an error in the estimated probability.
--
--   Let $\theta, \tilde\theta \in [0, 2\pi]$ and put $a = \sin^2\theta$, $\tilde a = \sin^2\tilde\theta$. For every real $\epsilon$,
--   $$|\theta - \tilde\theta| \le \epsilon \implies |a - \tilde a| \le 2\epsilon\sqrt{a(1-a)} + \epsilon^2.$$
--
--   It is used to turn the angle precision of phase estimation into the additive error of amplitude estimation.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 87, Proposition 4.19. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini p.87, Proposition 4.19 (Lem. 7 in Brassard et al. 2002): let `a = sin²θ` and
`ã = sin²θ̃` with `0 ≤ θ, θ̃ ≤ 2π`. Then `|θ − θ̃| ≤ ϵ` implies
`|a − ã| ≤ 2ϵ √(a(1 − a)) + ϵ²`. -/
theorem sinSq_angle_error (θ θt ε : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 2 * Real.pi)
    (hθt0 : 0 ≤ θt) (hθt1 : θt ≤ 2 * Real.pi) (h : |θ - θt| ≤ ε) :
    |Real.sin θ ^ 2 - Real.sin θt ^ 2| ≤
      2 * ε * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) + ε ^ 2 := by
  sorry



end QAlgorithms.Nannicini
