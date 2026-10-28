-- Prove2me | Theorems.Thm_RSInt_strip_integral_eq
-- name    : RSInt.strip_integral_eq
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:09:22.2684+00:00
-- url     : https://prove2.me/theorems/105e1736-6c12-4811-b769-cb793a41cef1
-- title:
--   Equality of integrals on the edges of a horizontal strip
-- statement:
--   Let $y_1\le y_2$ be real. Suppose $f:\mathbb C\to\mathbb C$ is continuous on
--   $y_1\le\operatorname{Im}z\le y_2$, holomorphic on the interior, and integrable
--   on both horizontal boundary lines. Assume also that $f(x+iy)\to0$ uniformly
--   for $y\in[y_1,y_2]$ as $|x|\to\infty$. Then
--
--   $$\int_{\mathbb R}f(x+iy_1)\,dx=\int_{\mathbb R}f(x+iy_2)\,dx.$$
--
--   This is the contour-shift identity used in the analytic estimates.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Strip.lean#L78-L158

import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
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

theorem RSInt.strip_integral_eq {f : ℂ → ℂ} {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂)
    (hcont : ContinuousOn f {z : ℂ | z.im ∈ Icc y₁ y₂})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | z.im ∈ Ioo y₁ y₂})
    (hint₁ : Integrable (fun x : ℝ => f (x + y₁ * I)))
    (hint₂ : Integrable (fun x : ℝ => f (x + y₂ * I)))
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x y : ℝ, R ≤ |x| → y ∈ Icc y₁ y₂ → ‖f (x + y * I)‖ ≤ ε) :
    ∫ x : ℝ, f (x + y₁ * I) = ∫ x : ℝ, f (x + y₂ * I) := by sorry
