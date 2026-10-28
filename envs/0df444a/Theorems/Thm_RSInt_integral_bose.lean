-- Prove2me | Theorems.Thm_RSInt_integral_bose
-- name    : RSInt.integral_bose
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:05:21.17856+00:00
-- url     : https://prove2.me/theorems/2549084d-2ce5-4266-ba8c-fa0a6bd96c18
-- title:
--   A Bose-type integral for the zeta function
-- statement:
--   For $s\in\mathbb C$ with $\operatorname{Re}s>1$, using principal complex powers,
--
--   $$\int_0^\infty\frac{\rho^{s-1}}{e^{(1+i)\rho}-1}\,d\rho
--   =(1+i)^{-s}\Gamma(s)\zeta(s).$$
--
--   This evaluates the positive-real-axis integral appearing in the contour argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Mellin.lean#L324-L405

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integral_cpow_mul_exp_neg_mul_Ioi_complex
import Theorems.Thm_RSInt_one_div_mul_cpow
/-  RS_Mellin.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 3:
    the Mellin step.  Mathlib-only (imports `RS_Kernel`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integral_cpow_mul_exp_neg_mul_Ioi_complex` : the complex-scaled Gamma integral
            int_0^oo rho^(s-1) e^(-z rho) d rho = (1/z)^s Gamma(s),     Re s > 0, Re z > 0,
        extending Mathlib's real-`z` lemma by the identity theorem.
      * `one_div_mul_cpow` : the branch bookkeeping (1/(x(1+i)))^s = x^(-s) (1+i)^(-s) whenever
        Re(x(1+i)) > 0.
      * `mellin_step` : Fubini on (line) x (0, oo):
            Gamma(s) lineUp c (rsG x^(-s)) = (1+i)^s int_0^oo rho^(s-1) rsK c ((1+i) rho) d rho,
        with rsK c y = lineUp c (rsG e^(-x y)) the Mordell integral.
      * `rsK_split` : the Mordell closed form at y = (1+i) rho, split into the Bose kernel and the
        Gaussian (chi-side) kernel.
      * `integral_bose` : int_0^oo rho^(s-1) / (e^((1+i) rho) - 1) = (1+i)^(-s) Gamma(s) zeta(s),
        Re s > 1 (geometric series, termwise integration, Mathlib's Dirichlet series for zeta).
      * `integral_Epart` : the chi-side kernel integral equals (2 pi)^s (1-i)^(-s) rsHR s, where
        rsHR s = int_0^oo rsH(r(1-i)) (r(1-i))^(s-1) (1-i) dr is half of the chi-side line.
      * `mellin_identity` : for Re s > 1 and 0 < c < 1,
            Gamma(s) lineUp c (rsG x^(-s)) = -Gamma(s) zeta(s) + (2 pi)^s (1+i)^s (1-i)^(-s) rsHR s.

    conjecture1_proved = False.  Classical integral identities for zeta; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Integrability of `rho^a e^(-b rho)` and norms -/









/-! ## 2. Branch bookkeeping -/







/-! ## 3. The complex-scaled Gamma integral -/



/-! ## 4. The Mellin step (Fubini) -/













/-! ## 5. Splitting the Mordell kernel -/







/-! ## 6. The Bose integral -/

theorem RSInt.integral_bose {s : ℂ} (hs : 1 < s.re) :
    ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * (1 / (cexp ((1 + I) * ρ) - 1)) =
      (1 + I) ^ (-s) * Gamma s * riemannZeta s := by sorry
