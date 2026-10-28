-- Prove2me | Theorems.Thm_RSInt_integrable_of_continuous_of_tail
-- name    : RSInt.integrable_of_continuous_of_tail
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:53:02.707352+00:00
-- url     : https://prove2.me/theorems/ee53ee66-f67d-45a8-b41e-b1c7ae77b0ed
-- title:
--   Integrability from a Gaussian tail bound
-- statement:
--   Let $f:\mathbb R\to\mathbb C$ be continuous, let $a>0$, and let $b,C,R$ be
--   real numbers. Suppose that for every real $v$ with $|v|\ge R$,
--
--   $$|f(v)|\le C\,e^{-av^2+b|v|}.$$
--
--   Then $f$ is integrable over the real line.
--
--   This gives an integrability criterion for the contour kernels.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Strip.lean#L49-L74

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

theorem RSInt.integrable_of_continuous_of_tail {f : ℝ → ℂ} (hf : Continuous f) {a b C R : ℝ}
    (ha : 0 < a) (htail : ∀ v : ℝ, R ≤ |v| → ‖f v‖ ≤ C * Real.exp (-a * v ^ 2 + b * |v|)) :
    Integrable f := by sorry
