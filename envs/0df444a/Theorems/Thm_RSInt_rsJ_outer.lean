-- Prove2me | Theorems.Thm_RSInt_rsJ_outer
-- name    : RSInt.rsJ_outer
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:22:56.695083+00:00
-- url     : https://prove2.me/theorems/2d3a21cf-d605-4687-8d23-8edef0f153c9
-- title:
--   A lower-contour expression for the saddle integral
-- statement:
--   Let $0<p<1$, put $D(z)=e^{\pi iz}-e^{-\pi iz}$ and
--   $H(z)=e^{-\pi iz^2}/D(z)$, and let
--   $L_{\pm}(c,F)=\int_{\mathbb R}F(c+v(1\pm i))(1\pm i)\,dv$.
--   For $J(p)=L_+(0,w\mapsto e^{2\pi iw^2}/D(p+w))$,
--
--   $$\begin{aligned}
--   J(p)=e^{\pi i/4-2\pi ip^2}\bigl[&L_-(-p,y\mapsto H(y)e^{\pi i(1-4p)y})\\
--   &-L_-(-p,y\mapsto e^{-2\pi iy^2-4\pi ipy}/D(y))\bigr].
--   \end{aligned}$$
--
--   This representation is used to obtain the uniform bound for $J$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_C0.lean#L285-L335

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_mordell
import Theorems.Thm_RSInt_norm_rsH_mul_le
import Theorems.Thm_RSInt_rsJ_fubini
/-  RS_C0.lean -- lane RS, brick B3 (the Riemann-Siegel remainder), part 1: RIEMANN'S Psi.
    Mathlib-only (imports `RS_B2`).

    The main term of the Riemann-Siegel remainder is the Mordell integral with Gaussian e^{2 pi i w^2}
    (tau = 2):
        rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / (e^{i pi (p+w)} - e^{-i pi (p+w)})),   0 < p < 1.
    Its value is not elementary, but the combination that enters Z(t) is:

        2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p) = Psi(p)   (Gabcke's C0).

    Proof (no residue theorem): write e^{i pi w^2} as a Gaussian Fourier integral along the (1-i)
    line, swap the two line integrals (Fubini), evaluate the inner one by the tau = 1 Mordell closed
    form (RS_Kernel), split the outer one into a tau = -1 Mordell integral (closed form by conjugation
    and one pole crossing) and a tau = -2 integral that is the conjugate of rsJ itself (symmetry
    rsJ(1-p) = rsJ(p)).  This gives rsJ + e^{i pi/4} conj(rsJ) = elementary, whose real part after the
    phase e^{-i pi/8} is Psi.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Linearity for `lineDn`, translations -/









/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/





/-! ## 3. The tau = 2 Mordell integral and its symmetry -/















/-! ## 4. Fubini: rsJ as an iterated integral -/



/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/



/-! ## 6. The outer integral splits into T1 - T2 -/

theorem RSInt.rsJ_outer {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = cexp (↑π / 4 * I) * (cexp (-(2 * ↑π * I * p ^ 2)) *
      (lineDn (-p) (fun y => rsH y * cexp (↑π * I * (1 - 4 * p) * y)) -
        lineDn (-p) (fun y => cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y))) := by sorry
