-- Prove2me | Theorems.Thm_RSInt_rsJ_fubini
-- name    : RSInt.rsJ_fubini
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:08:00.746797+00:00
-- url     : https://prove2.me/theorems/64d16e34-6aca-440c-85c4-0f4dc742d38d
-- title:
--   A double-contour representation of the saddle integral
-- statement:
--   For $0<p<1$, set $D(z)=e^{\pi iz}-e^{-\pi iz}$ and define
--   $L_{\pm}(F)=\int_{\mathbb R}F(v(1\pm i))(1\pm i)\,dv$ and
--   $J(p)=L_+\bigl(w\mapsto e^{2\pi iw^2}/D(p+w)\bigr)$. Then
--
--   $$J(p)=e^{\pi i/4}L_-\!\left(u\mapsto e^{-\pi iu^2}
--   L_+\!\left(w\mapsto\frac{e^{\pi iw^2+2\pi iuw}}{D(p+w)}\right)\right).$$
--
--   This representation supports the bound on the saddle integral.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_C0.lean#L149-L205

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_gauss_fourier_dn
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
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

theorem RSInt.rsJ_fubini {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = cexp (↑π / 4 * I) * lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2)) *
      lineUp 0 (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w))) := by sorry
