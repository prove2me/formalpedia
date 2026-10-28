-- Prove2me | Theorems.Thm_RSInt_differentiable_rsA
-- name    : RSInt.differentiable_rsA
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:00:56.955465+00:00
-- url     : https://prove2.me/theorems/ddbf6f4b-856f-430d-86e8-6ff2dd2e0403
-- title:
--   Analytic dependence of the upper Riemann contour integral
-- statement:
--   Let $c>0$ be real and not an integer. Define
--   $D(z)=e^{\pi iz}-e^{-\pi iz}$ and $G(z)=e^{\pi iz^2}/D(z)$.
--   Using principal complex powers, the function
--
--   $$s\longmapsto\int_{\mathbb R}G(c+v(1+i))(c+v(1+i))^{-s}(1+i)\,dv$$
--
--   is complex differentiable on $\mathbb C$.
--
--   This analyticity supports extension of the contour identity.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Entire.lean#L227-L249

import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_differentiable_integral_cpow
import Theorems.Thm_RSInt_norm_rsG_le
/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/







/-! ## 2. The two Riemann-Siegel line integrals are entire in `s` -/

theorem RSInt.differentiable_rsA {c : ℝ} (hc : 0 < c) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Differentiable ℂ (fun s : ℂ => lineUp c (fun x => rsG x * x ^ (-s))) := by sorry
