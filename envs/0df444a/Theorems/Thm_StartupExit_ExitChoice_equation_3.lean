-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_equation_3
-- name    : StartupExit.ExitChoice.equation_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:43.265292+00:00
-- url     : https://prove2.me/theorems/3c417748-9943-4112-955e-59668cf73c3d
-- title:
--   Eq. (3), p. 18, with p. 12 — θ̃, the unique θ with Π^E = Π^L, equals (w + (m−3)/(m+1))/(w + (n−3)/(n+1)) and lies in (0, 1)
-- statement:
--   Under the standing assumptions ($w>1$, $2\le m<n$), let $\tilde\theta=\Pi^E/(w+X(2,n))$. Then $\tilde\theta$ is the unique $\theta$ at which committing early and committing late pay the same,
--
--   $$\Pi^E=\Pi^L(\theta)\iff\theta=\tilde\theta,$$
--
--   it lies strictly between $0$ and $1$, and it has the closed form
--
--   $$\tilde\theta=\frac{w+\frac{m-3}{m+1}}{w+\frac{n-3}{n+1}} .$$
--
--   $\tilde\theta$ is the threshold separating early from late commitment when the early market is costly (Proposition 1 (iii)).
--
--   **Formalization Note** The page defines $\tilde\theta$ as the unique solution of $\Pi^E=\Pi^L$ (p. 12) and gives the closed form (3) on p. 18; both are stated here, the first as an equivalence over all real $\theta$.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), p. 12 (PDF 13), definition of θ̃; p. 18 (PDF 19), eq. (3)

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem equation_3 (P : Params) (hS : P.Standing) :
    0 < thetaTilde P ∧ thetaTilde P < 1 ∧
    (∀ θ : ℝ, PiE P = PiL P θ ↔ θ = thetaTilde P) ∧
    thetaTilde P =
      (P.w + ((P.m : ℝ) - 3) / ((P.m : ℝ) + 1)) /
        (P.w + ((P.n : ℝ) - 3) / ((P.n : ℝ) + 1)) := by sorry

end StartupExit.ExitChoice
