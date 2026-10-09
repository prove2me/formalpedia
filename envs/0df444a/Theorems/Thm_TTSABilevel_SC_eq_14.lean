-- Prove2me | Theorems.Thm_TTSABilevel_SC_eq_14
-- name    : TTSABilevel.SC.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:10.790395+00:00
-- url     : https://prove2.me/theorems/9704abc7-9765-4055-8604-e863755dd90e
-- title:
--   Equation (14): conditional second moment of the outer estimate
-- statement:
--   In the TTSA run under Assumptions 1–3, let $\mathcal F'_k$ contain the history through $y^{k+1}$, let $b_k$ bound the outer-estimate bias, and let $\widetilde\sigma_f^2=\sigma_f^2+3\sup_{x\in X}\|\nabla\ell(x)\|^2$ be finite. Then for every $k\ge0$,
--
--   $$
--   \mathbb E[\|h_f^k\|^2\mid\mathcal F'_k]\le
--   \widetilde\sigma_f^2+3b_k^2+3L^2\|y^{k+1}-y^\star(x^k)\|^2.
--   $$
--
--   This bounds the outer stochastic estimate in terms of inner tracking and the paper’s variance and bias quantities. The inequality holds almost surely.
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, p. 8, (14) and standing boundedness assumption immediately below it

import Mathlib
import Definitions.Def_TTSABilevel_SC_Setting

open MeasureTheory

namespace TTSABilevel.SC

theorem eq_14 {d1 d2 : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Set (E1 d1)) (f g : E1 d1 → E2 d2 → ℝ)
    (ystar : E1 d1 → E2 d2) (proj : E1 d1 → E1 d1)
    (α β : ℕ → ℝ) (x0 : E1 d1) (y0 : E2 d2)
    (x : ℕ → Ω → E1 d1) (y : ℕ → Ω → E2 d2)
    (hg : ℕ → Ω → E2 d2) (hf B : ℕ → Ω → E1 d1)
    (Lfx Lfy Lfybar Cfy Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy σg σf : ℝ)
    (b : ℕ → ℝ)
    (hclosed : IsClosed X) (hconvex : Convex ℝ X)
    (hf1 : ContDiff ℝ 1 (Function.uncurry f))
    (h1 : Asm1 f X Lfx Lfy Lfybar Cfy)
    (h2 : Asm2 g X Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy)
    (hinner : IsInnerSol g X ystar)
    (hrun : IsTTSARun P X proj α β x0 y0 x y hg hf)
    (h3 : Asm3 P f g ystar x y hg hf B σg σf b)
    (hbounded : BddAbove ((fun z : E1 d1 => ‖gradEll f g ystar z‖ ^ 2) '' X)) :
    ∀ k : ℕ,
      P[fun ω => ‖hf k ω‖ ^ 2|Fk' x y k] ≤ᵐ[P]
        fun ω => sigTilde2 σf X f g ystar + 3 * b k ^ 2 +
          3 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2 *
            ‖y (k + 1) ω - ystar (x k ω)‖ ^ 2 := by sorry

end TTSABilevel.SC
