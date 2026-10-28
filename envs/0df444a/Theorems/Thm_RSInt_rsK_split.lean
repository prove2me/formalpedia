-- Prove2me | Theorems.Thm_RSInt_rsK_split
-- name    : RSInt.rsK_split
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:23:51.154296+00:00
-- url     : https://prove2.me/theorems/9b0c969f-7bc9-40ad-8d1a-f95b65c89236
-- title:
--   Closed expression for the upper-kernel transform
-- statement:
--   Let $0<c<1$ and $\rho>0$ be real. Put $y=(1+i)\rho$,
--   $D(z)=e^{\pi iz}-e^{-\pi iz}$, $G(z)=e^{\pi iz^2}/D(z)$, and
--   $K(c,y)=\int_{\mathbb R}G(c+v(1+i))e^{-(c+v(1+i))y}(1+i)\,dv$. Then
--
--   $$K(c,y)=-\frac1{e^y-1}+\frac{e^{iy^2/(4\pi)}}{e^{y/2}-e^{-y/2}}.$$
--
--   This splits the transform into a Bose term and a correction term.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Mellin.lean#L280-L315

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_lineUp_mordell
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

theorem RSInt.rsK_split {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    rsK c ((1 + I) * ρ) = -(1 / (cexp ((1 + I) * ρ) - 1)) +
      cexp (I * ((1 + I) * ρ) ^ 2 / (4 * ↑π)) /
        (cexp ((1 + I) * ρ / 2) - cexp (-((1 + I) * ρ / 2))) := by sorry
