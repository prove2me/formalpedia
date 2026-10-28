-- Prove2me | Theorems.Thm_RSInt_rsJ_C0
-- name    : RSInt.rsJ_C0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:26:44.810404+00:00
-- url     : https://prove2.me/theorems/7b6a893f-d349-4131-8db0-c512e6b6725f
-- title:
--   Real part of the saddle integral
-- statement:
--   Let $0<p<1$ be real and suppose $\cos(2\pi p)\ne0$. With
--   $D(z)=e^{\pi iz}-e^{-\pi iz}$, define
--
--   $$J(p)=\int_{\mathbb R}\frac{e^{2\pi i(v(1+i))^2}}{D(p+v(1+i))}(1+i)\,dv.$$
--
--   Then
--
--   $$2\operatorname{Re}\!\left(e^{-\pi i/8}J(p)\right)
--   =\frac{\cos(2\pi(p^2-p-1/16))}{\cos(2\pi p)}.$$
--
--   This identifies the leading correction in the Riemann–Siegel formula.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_C0.lean#L396-L510

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_lineUp_cross
import Theorems.Thm_RSInt_lineUp_mordell
import Theorems.Thm_RSInt_rsJ_outer
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









/-! ## 7. T2 is the conjugate of rsJ; T1 by one pole crossing and the Mordell formula -/







/-! ## 8. Riemann's Psi -/

theorem RSInt.rsJ_C0 {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hcos : Real.cos (2 * π * p) ≠ 0) :
    2 * (cexp (-(↑π / 8 * I)) * rsJ p).re =
      Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p) := by sorry
