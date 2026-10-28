-- Prove2me | Theorems.Thm_RSInt_mellin_step
-- name    : RSInt.mellin_step
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:05:28.514519+00:00
-- url     : https://prove2.me/theorems/7d50beb2-2b5d-4685-a540-8d4b0a33af1e
-- title:
--   Mellin relation for the upper Riemann contour
-- statement:
--   Let $0<c<1$ and $s\in\mathbb C$ with $\operatorname{Re}s>0$. Define
--   $D(z)=e^{\pi iz}-e^{-\pi iz}$, $G(z)=e^{\pi iz^2}/D(z)$, and
--   $L_+(c,F)=\int_{\mathbb R}F(c+v(1+i))(1+i)\,dv$. Set
--   $K(c,y)=L_+(c,z\mapsto G(z)e^{-zy})$. With principal complex powers,
--
--   $$\Gamma(s)L_+(c,z\mapsto G(z)z^{-s})
--   =(1+i)^s\int_0^\infty\rho^{s-1}K(c,(1+i)\rho)\,d\rho.$$
--
--   This relates the contour integral to a Mellin transform.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Mellin.lean#L211-L266

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_lineUp_rsG_mul
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

theorem RSInt.mellin_step {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {s : ℂ} (hs : 0 < s.re) :
    Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) =
      (1 + I) ^ s * ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (s - 1) * rsK c ((1 + I) * ρ) := by sorry
