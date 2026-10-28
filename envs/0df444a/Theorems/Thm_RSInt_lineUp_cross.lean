-- Prove2me | Theorems.Thm_RSInt_lineUp_cross
-- name    : RSInt.lineUp_cross
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:17:36.465922+00:00
-- url     : https://prove2.me/theorems/c60d6817-e946-405c-bb0d-a9b14ff264ba
-- title:
--   Crossing an integer pole in an upper-contour integral
-- statement:
--   Let $n$ be an integer and $c_1,c_2$ real with $n-1<c_1<n<c_2<n+1$.
--   Let $\phi:\mathbb C\to\mathbb C$ be complex differentiable throughout
--   $c_1\le\operatorname{Re}z-\operatorname{Im}z\le c_2$ and satisfy
--   $|\phi(z)|\le A e^{B|z|}$ there for real constants $A,B$. Put
--   $D(z)=e^{\pi iz}-e^{-\pi iz}$, $G(z)=e^{\pi iz^2}/D(z)$, and
--   $L_+(c,F)=\int_{\mathbb R}F(c+v(1+i))(1+i)\,dv$. Then
--
--   $$L_+(c_2,G\phi)=L_+(c_1,G\phi)+\phi(n).$$
--
--   This identifies the contribution of a crossed kernel pole.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Kernel.lean#L696-L804

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_deriv_rsD_int_ne_zero
import Theorems.Thm_RSInt_integrable_lineUp_rsG_mul
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_eq_of_strip
import Theorems.Thm_RSInt_lineUp_rsG_jump
import Theorems.Thm_RSInt_norm_rsG_mul_le
/-  RS_Kernel.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 2:
    Riemann's kernels, their difference equations, Gaussian bounds, the Fresnel line integral,
    the pole-crossing lemmas and the Mordell closed form.

    Mathlib-only (imports `RS_Strip` only).

    ## The kernels

        rsD x = e^{i pi x} - e^{-i pi x}          (= 2 i sin(pi x); zeros exactly at the integers)
        rsG x = e^{ i pi x^2} / rsD x              (Riemann's kernel of the zeta integral)
        rsH x = e^{-i pi x^2} / rsD x              (the kernel of the chi-side integral)

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `rsD_eq_zero_iff`, `rsD_add_one`, `rsG_add_one`, `rsH_add_one` : zeros and the difference
        equations  rsG(x+1) = rsG x + e^{i pi (x^2+x)},  rsH(x+1) = rsH x - e^{-i pi (x^2+x)}.
      * `norm_rsG_le`, `norm_rsH_le` : on a slanted strip, away from the real axis (|Im x| >= 1), the
        kernels are bounded by exp(-2 pi (Im x)^2 + 2 pi D |Im x|)  (Gaussian decay).
      * `lineUp_fresnel`, `lineUp_gauss` : the Gaussian line integrals, e.g.
            lineUp c (x |-> e^{i pi (x^2+x) - x y}) = e^{y/2 + i y^2/(4 pi)}     (every c, every y).
      * `lineUp_same_gap`, `lineUp_cross` : moving the slope-(+1) line inside a gap (n, n+1) changes
        nothing; moving it across the pole at the integer n adds phi(n):
            lineUp c2 (rsG * phi) = lineUp c1 (rsG * phi) + phi n,   n-1 < c1 < n < c2 < n+1,
        for every phi holomorphic on the strip with at most exponential growth.  No residue theorem
        is used: the pole is removed by `dslope`, and the jump of the bare kernel is computed from
        the difference equation and the Fresnel integral.
      * `lineDn_same_gap`, `lineDn_cross` : the slope-(-1) analogues for rsH (by conjugation).
      * `lineUp_mordell` : the Mordell closed form, for 0 < c < 1 and every y:
            lineUp c (x |-> rsG x e^{-x y}) (e^{-y/2} - e^{y/2}) = e^{-y/2} - e^{i y^2/(4 pi)}.

    conjecture1_proved = False.  Contour identities for one explicit kernel; nothing here bears
    on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. The kernels and their algebra -/



























/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/













/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/

theorem RSInt.lineUp_cross {φ : ℂ → ℂ} {n : ℤ} {c₁ c₂ : ℝ}
    (h₁ : (n : ℝ) - 1 < c₁) (h₁' : c₁ < n) (h₂ : (n : ℝ) < c₂) (h₂' : c₂ < n + 1)
    (hφ : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ φ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineUp c₂ (fun x => rsG x * φ x) = lineUp c₁ (fun x => rsG x * φ x) + φ n := by sorry
