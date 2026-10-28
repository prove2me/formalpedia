-- Prove2me | Theorems.Thm_RSInt_norm_rsH_mul_le
-- name    : RSInt.norm_rsH_mul_le
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:02:19.037245+00:00
-- url     : https://prove2.me/theorems/76eedc02-b859-4529-b8f9-d71a4b393f9d
-- title:
--   Gaussian tail bound for a lower-kernel product
-- statement:
--   Let $D(z)=e^{\pi iz}-e^{-\pi iz}$, $H(z)=e^{-\pi iz^2}/D(z)$, and
--   $\psi:\mathbb C\to\mathbb C$. Let $z=x+iy$ and $c_1,c_2,A,B$ be real, with
--   $c_1\le x+y\le c_2$, $|y|\ge1$, and $|\psi(z)|\le A e^{B|z|}$. Put
--   $C=|c_1|+|c_2|$. Then
--
--   $$|H(z)\psi(z)|\le |A|e^{|B|C}
--   e^{-2\pi y^2+(2\pi C+2|B|)|y|}.$$
--
--   This majorant controls products with the lower contour kernel.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Kernel.lean#L482-L509

import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_norm_rsH_le
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

theorem RSInt.norm_rsH_mul_le {ψ : ℂ → ℂ} {c₁ c₂ A B : ℝ} {x : ℂ} (hx : x.re + x.im ∈ Icc c₁ c₂)
    (h1 : 1 ≤ |x.im|) (hψ : ‖ψ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    ‖rsH x * ψ x‖ ≤ (|A| * Real.exp (|B| * (|c₁| + |c₂|))) *
      Real.exp (-(2 * π) * x.im ^ 2 + (2 * π * (|c₁| + |c₂|) + 2 * |B|) * |x.im|) := by sorry
