-- Prove2me | Theorems.Thm_TTSABilevel_SC_lemma_2_12a
-- name    : TTSABilevel.SC.lemma_2_12a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:14.775826+00:00
-- url     : https://prove2.me/theorems/576f84a7-a4b9-468b-9655-579b43a88ad5
-- title:
--   Lemma 2 (12a): surrogate and inner-solution Lipschitz bounds
-- statement:
--   Under Assumptions 1 and 2, let $y^\star(x)$ solve the inner problem for each $x\in X$. With $L$ and $L_y$ fixed by (13), for $x,x_1,x_2\in X$ and $y\in\mathbb R^{d_2}$,
--
--   $$
--   \|\bar\nabla_x f(x,y)-\nabla\ell(x)\|\le L\|y^\star(x)-y\|,\qquad
--   \|y^\star(x_1)-y^\star(x_2)\|\le L_y\|x_1-x_2\|.
--   $$
--
--   The two estimates connect inner tracking error to the outer surrogate and to the motion of the inner minimizer.
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, pp. 7–8, Lemma 2 (12a) and constants (13)

import Mathlib
import Definitions.Def_TTSABilevel_SC_Setting

namespace TTSABilevel.SC

theorem lemma_2_12a {d1 d2 : ℕ} (X : Set (E1 d1))
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (f g : E1 d1 → E2 d2 → ℝ) (ystar : E1 d1 → E2 d2)
    (Lfx Lfy Lfybar Cfy Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy : ℝ)
    (hclosed : IsClosed X) (hconvex : Convex ℝ X)
    (hf1 : ContDiff ℝ 1 (Function.uncurry f))
    (h1 : Asm1 f X Lfx Lfy Lfybar Cfy)
    (h2 : Asm2 g X Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy)
    (hinner : IsInnerSol g X ystar) :
    (∀ x ∈ X, ∀ y,
      ‖surr f g x y - gradEll f g ystar x‖ ≤
        Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy * ‖ystar x - y‖) ∧
    (∀ x1 ∈ X, ∀ x2 ∈ X,
      ‖ystar x1 - ystar x2‖ ≤ Lyconst Cgxy μg * ‖x1 - x2‖) := by sorry

end TTSABilevel.SC
