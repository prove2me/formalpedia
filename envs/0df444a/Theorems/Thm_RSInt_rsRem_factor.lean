-- Prove2me | Theorems.Thm_RSInt_rsRem_factor
-- name    : RSInt.rsRem_factor
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:16:08.48778+00:00
-- url     : https://prove2.me/theorems/312e4e34-6981-4d31-abf7-0b152cdf683b
-- title:
--   Factorization of the Riemann–Siegel remainder integral
-- statement:
--   Let $t>0$, $a=\sqrt{t/(2\pi)}$, $N=\lfloor a\rfloor_{\mathbb N}$, and
--   $p=a-N>0$. Put $D(z)=e^{\pi iz}-e^{-\pi iz}$,
--   $G(z)=e^{\pi iz^2}/D(z)$, and
--   $\Phi_a(w)=e^{2\pi iaw-\pi iw^2}(1+w/a)^{-1/2-2\pi ia^2}$, with principal
--   complex powers. For $L_+(c,F)=\int_{\mathbb R}F(c+v(1+i))(1+i)\,dv$, define
--
--   $$\begin{aligned}
--   R(t)&=-L_+(N+1/2,z\mapsto G(z)z^{-1/2-it}),\\
--   J(p)&=L_+(0,w\mapsto e^{2\pi iw^2}/D(p+w)),\\
--   E_1(a,p)&=L_+(0,w\mapsto e^{2\pi iw^2}(\Phi_a(w)-1)/D(p+w)).
--   \end{aligned}$$
--
--   Then
--
--   $$R(t)=(-1)^{N+1}e^{\pi ia^2}a^{-1/2-it}\bigl(J(p)+E_1(a,p)\bigr).$$
--
--   This separates the saddle integral from the analytic remainder.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_B3.lean#L160-L214

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_lineUp_rsG_mul
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_cpow_same_gap
import Theorems.Thm_RSInt_norm_cpow_le_of_ge
import Theorems.Thm_RSInt_rsG_cpow_factor
/-  RS_B3.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 2: the exact
    saddle-point reduction.  Mathlib-only (imports `RS_C0`).

    ## Vocabulary (height t > 0)

        a = rsAlpha t = sqrt(t / 2 pi),  N = rsNn t = floor a,  p = rsFrac t = a - N,
        rsThetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8   (verbatim the corpus thetaMain),
        rsPsi p = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)            (Gabcke's C0 = Riemann's Psi),
        rsRem t = -lineUp (N + 1/2) (x |-> rsG x x^(-(1/2 + i t)))    (the exact RS remainder, B2).

    By B2 (`completed_re_eq_rs_cos`), on the critical line
        Re completedRiemannZeta(1/2+it) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} rsRem t) ).

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms)

      * `rsRem_factor` : moving the remainder line to the saddle point a and factoring out the
        stationary phase,
            rsRem t = (-1)^(N+1) e^{i pi a^2} a^(-s) (rsJ p + rsE1 a p),
        where rsJ is the tau = 2 Mordell integral (RS_C0) and rsE1 the error integral of the amplitude
        rsPhi a w - 1,  rsPhi a w = e^{2 pi i a w - pi i w^2} (1 + w/a)^(-s).
      * `rs_phase` : e^{i phi} e^{i pi a^2} a^(-s) = a^(-1/2) e^{i (phi - rsThetaMain t - pi/8)}.
      * `rs_remainder_exact` : the EXACT identity
            2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
              = (-1)^(N+1) a^(-1/2) [ 2 Re(e^{-i pi/8}(e^{i delta} - 1) rsJ p)
                                      + 2 Re(e^{i (delta - pi/8)} rsE1 a p) ],   delta = phi - thetaMain t,
        so the C0-corrected remainder is controlled by |delta| |rsJ p| and |rsE1 a p| alone.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 0. Vocabulary -/































/-! ## 1. Shifting the denominator by an integer -/



/-! ## 2. The factorization at the saddle point -/

theorem RSInt.rsRem_factor {t : ℝ} (ht : 0 < t) (hp : 0 < rsFrac t) :
    rsRem t = (-1) ^ (rsNn t + 1) * cexp (↑π * I * (rsAlpha t) ^ 2) *
      ((rsAlpha t : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) *
        (rsJ (rsFrac t) + rsE1 (rsAlpha t) (rsFrac t)) := by sorry
