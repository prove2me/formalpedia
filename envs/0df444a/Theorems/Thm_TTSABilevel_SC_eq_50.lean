-- Prove2me | Theorems.Thm_TTSABilevel_SC_eq_50
-- name    : TTSABilevel.SC.eq_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:25.540495+00:00
-- url     : https://prove2.me/theorems/3d64d8b1-4e28-40e8-ba73-13ecbb738684
-- title:
--   Equation (50): one-step inner tracking contraction
-- statement:
--   For the TTSA inner update under Assumptions 2 and 3, suppose $\beta_k\ge0$ and $\beta_kL_g^2(1+\sigma_g^2)\le\mu_g$. Conditional on the history $\mathcal F_k$ through $(x^k,y^k)$,
--
--   $$
--   \mathbb E[\|y^{k+1}-y^\star(x^k)\|^2\mid\mathcal F_k]
--   \le (1-\beta_k\mu_g)\|y^k-y^\star(x^k)\|^2+\beta_k^2\sigma_g^2.
--   $$
--
--   The inequality is almost sure and is the one-step contraction that starts the tracking-error analysis.
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, p. 20, App. A.1, (50)

import Mathlib
import Definitions.Def_TTSABilevel_SC_Setting

open MeasureTheory

namespace TTSABilevel.SC

theorem eq_50 {d1 d2 : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Set (E1 d1)) (f g : E1 d1 → E2 d2 → ℝ)
    (ystar : E1 d1 → E2 d2) (proj : E1 d1 → E1 d1)
    (α β : ℕ → ℝ) (x0 : E1 d1) (y0 : E2 d2)
    (x : ℕ → Ω → E1 d1) (y : ℕ → Ω → E2 d2)
    (hg : ℕ → Ω → E2 d2) (hf B : ℕ → Ω → E1 d1)
    (Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy σg σf : ℝ) (b : ℕ → ℝ)
    (hclosed : IsClosed X) (hconvex : Convex ℝ X)
    (h2 : Asm2 g X Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy)
    (hinner : IsInnerSol g X ystar)
    (hrun : IsTTSARun P X proj α β x0 y0 x y hg hf)
    (h3 : Asm3 P f g ystar x y hg hf B σg σf b)
    (k : ℕ) (hβ : 0 ≤ β k)
    (hstep : β k * Lg ^ 2 * (1 + σg ^ 2) ≤ μg) :
    P[fun ω => ‖y (k + 1) ω - ystar (x k ω)‖ ^ 2|Fk x y k] ≤ᵐ[P]
      fun ω => (1 - β k * μg) * ‖y k ω - ystar (x k ω)‖ ^ 2 + β k ^ 2 * σg ^ 2 := by sorry

end TTSABilevel.SC
