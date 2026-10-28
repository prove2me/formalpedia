-- Prove2me | Theorems.Thm_RSInt_gauss_fourier_dn
-- name    : RSInt.gauss_fourier_dn
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:51:48.581082+00:00
-- url     : https://prove2.me/theorems/7cd0c43f-005c-4c85-818c-0ff07a3bcb5b
-- title:
--   Fourier transform of a Gaussian along a diagonal line
-- statement:
--   For a complex $w$, let $L_-(F)=\int_{\mathbb R}F(v(1-i))(1-i)\,dv$.
--   Then
--
--   $$e^{\pi i w^2}=e^{\pi i/4}\,
--   L_-\!\left(u\mapsto e^{-\pi i u^2+2\pi iuw}\right).$$
--
--   This diagonal Gaussian identity supplies a contour-transform step.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_C0.lean#L66-L90

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
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

theorem RSInt.gauss_fourier_dn (w : ℂ) :
    cexp (↑π * I * w ^ 2) =
      cexp (↑π / 4 * I) * lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2) + 2 * ↑π * I * u * w)) := by sorry
