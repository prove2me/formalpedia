-- Prove2me | Theorems.Thm_TTSABilevel_SC_eq_55
-- name    : TTSABilevel.SC.eq_55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:15.708775+00:00
-- url     : https://prove2.me/theorems/1db2159b-385b-4924-8405-e021efd5c6f8
-- title:
--   Equation (55): explicit inner tracking-error bound
-- statement:
--   Under the TTSA hypotheses of Theorem 1 needed for inner tracking, let $\Delta_y^k=\mathbb E\|y^k-y^\star(x^{k-1})\|^2$, where $x^{-1}=x^0$. Let $G^{(1)}_{m:n}=\prod_{i=m}^n(1-\beta_i\mu_g/4)$ and let $C_y^{(1)}$ be the explicit constant in (55). Then for every $k\ge0$,
--
--   $$
--   \Delta_y^{k+1}\le G^{(1)}_{0:k}\Delta_y^0+C_y^{(1)}\beta_k,\qquad
--   C_y^{(1)}=\frac8{\mu_g}\left\{\sigma_g^2+\frac{4c_0^2L_y^2}{\mu_g}(\widetilde\sigma_f^2+3b_0^2)\right\}.
--   $$
--
--   This is the explicit tracking bound used to obtain the outer error bound. The statement uses the factor $1/4$ printed in (55).
-- source:
--   Hong, Wai, Wang & Yang, A Two-Timescale Stochastic Algorithm Framework for Bilevel Optimization: Complexity Analysis and Application to Actor-Critic, arXiv:2007.05170v4, p. 21, App. A.1, (55)

import Mathlib
import Definitions.Def_TTSABilevel_SC_Setting

open MeasureTheory

namespace TTSABilevel.SC

theorem eq_55 {d1 d2 : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Set (E1 d1)) (f g : E1 d1 → E2 d2 → ℝ)
    (ystar : E1 d1 → E2 d2) (proj : E1 d1 → E1 d1)
    (α β : ℕ → ℝ) (x0 : E1 d1) (y0 : E2 d2)
    (x : ℕ → Ω → E1 d1) (y : ℕ → Ω → E2 d2)
    (hg : ℕ → Ω → E2 d2) (hf B : ℕ → Ω → E1 d1)
    (Lfx Lfy Lfybar Cfy Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy σg σf : ℝ)
    (b : ℕ → ℝ) (μℓ c0 c1 : ℝ)
    (hclosed : IsClosed X) (hconvex : Convex ℝ X)
    (hf1 : ContDiff ℝ 1 (Function.uncurry f))
    (h1 : Asm1 f X Lfx Lfy Lfybar Cfy)
    (h2 : Asm2 g X Lg μg Lgxy Lgyy Lgxybar Lgyybar Cgxy)
    (hinner : IsInnerSol g X ystar)
    (hrun : IsTTSARun P X proj α β x0 y0 x y hg hf)
    (h3 : Asm3 P f g ystar x y hg hf B σg σf b)
    (hbounded : BddAbove ((fun z : E1 d1 => ‖gradEll f g ystar z‖ ^ 2) '' X))
    (hμℓ : 0 < μℓ) (hc0 : 0 < c0) (hc1 : 0 < c1)
    (hαpos : ∀ k, 0 < α k) (hβpos : ∀ k, 0 < β k)
    (hαmono : Antitone α) (hβmono : Antitone β)
    (hαβ : ∀ k, α k ≤ c0 * (β k) ^ ((3 : ℝ) / 2))
    (hβα : ∀ k, β k ≤ c1 * (α k) ^ ((2 : ℝ) / 3))
    (hβratio : ∀ k, 1 ≤ k → β (k - 1) ≤ (1 + β k * μg / 8) * β k)
    (hαratio : ∀ k, 1 ≤ k → α (k - 1) ≤ (1 + 3 * α k * μℓ / 4) * α k)
    (hαmax : ∀ k, α k ≤ 1 / μℓ)
    (hβmax1 : ∀ k, β k ≤ 1 / μg)
    (hβmax2 : ∀ k, β k ≤ μg / (Lg ^ 2 * (1 + σg ^ 2)))
    (hβmax3 : ∀ k, β k ≤ μg ^ 2 /
      (48 * c0 ^ 2 * (Lconst Lfx Lfy Cgxy μg Cfy Lgxy Lgyy) ^ 2 *
        (Lyconst Cgxy μg) ^ 2))
    (hscale : ∀ k, 8 * μℓ * α k ≤ μg * β k) :
    ∀ k : ℕ,
      Dy P ystar x y (k + 1) ≤
        G1 β μg 0 k * Dy P ystar x y 0 +
          Cy1 μg σg c0 Cgxy σf b X f g ystar * β k := by sorry

end TTSABilevel.SC
