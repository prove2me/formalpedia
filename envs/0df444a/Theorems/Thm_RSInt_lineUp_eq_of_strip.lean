-- Prove2me | Theorems.Thm_RSInt_lineUp_eq_of_strip
-- name    : RSInt.lineUp_eq_of_strip
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:11:47.402743+00:00
-- url     : https://prove2.me/theorems/6e974079-218d-4d95-83c1-0d2fc034f2f4
-- title:
--   Invariance of an upward diagonal contour integral
-- statement:
--   Let $c_1\le c_2$ be real, and let $F:\mathbb C\to\mathbb C$ be continuous
--   on $c_1\le\operatorname{Re}z-\operatorname{Im}z\le c_2$ and holomorphic in
--   its interior. Suppose $F(c_j+v(1+i))$ is integrable in $v$ for $j=1,2$ and
--   $F(z)\to0$ uniformly as $|z|\to\infty$ within the closed strip. Then
--
--   $$\int_{\mathbb R}F(c_1+v(1+i))(1+i)\,dv
--   =\int_{\mathbb R}F(c_2+v(1+i))(1+i)\,dv.$$
--
--   This permits shifting the upward diagonal contour inside the strip.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Strip.lean#L216-L275

import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_strip_integral_eq
/-  RS_Strip.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 1:
    contour tools.

    Mathlib-only (no corpus import), so the file can serve the dbn island's M5 layer L6 as well.

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integrable_exp_quad`, `integrable_of_continuous_of_tail` : integrability of a continuous
        function from a Gaussian-type tail bound `C exp(-a v^2 + b |v|)`.
      * `strip_integral_eq` : Cauchy's theorem on a HORIZONTAL STRIP y1 <= Im z <= y2 with decay at
        both ends: the integrals along the two edges agree.  (Mathlib's rectangle theorem
        `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` plus two limits.)
      * `lineUp c F`, `lineDn c F` : the oriented integrals along the slanted lines through the real
        point `c` with directions `1 + I` (slope +1) and `1 - I` (slope -1).
      * `lineUp_eq_of_strip`, `lineDn_eq_of_strip` : line independence -- the integral along the line
        through `c1` equals the one through `c2` when `F` is continuous on the closed slanted strip,
        holomorphic inside, and tends to 0 at infinity in the strip.

    conjecture1_proved = False.  Contour-integration infrastructure; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Integrability from a Gaussian tail -/







/-! ## 2. Cauchy's theorem on a horizontal strip -/



/-! ## 3. Slanted lines -/

theorem RSInt.lineUp_eq_of_strip {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂})
    (hint₁ : Integrable (fun v : ℝ => F (c₁ + v * (1 + I))))
    (hint₂ : Integrable (fun v : ℝ => F (c₂ + v * (1 + I))))
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → R ≤ ‖x‖ → ‖F x‖ ≤ ε) :
    lineUp c₁ F = lineUp c₂ F := by sorry
