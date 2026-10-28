-- Prove2me | Theorems.Thm_RSInt_rs_remainder_exact
-- name    : RSInt.rs_remainder_exact
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:29:47.649598+00:00
-- url     : https://prove2.me/theorems/0030c308-40be-48d6-83d0-215d57c22d98
-- title:
--   Exact decomposition of the Riemann–Siegel remainder
-- statement:
--   Let $t>0$ be real, $a=\sqrt{t/(2\pi)}$, $N=\lfloor a\rfloor_{\mathbb N}$,
--   and $p=a-N>0$ with $\cos(2\pi p)\ne0$. Let $\phi$ be real and define
--
--   $$\theta_{\rm main}=\frac t2\log t-\frac t2\log(2\pi)-\frac t2-\frac\pi8,
--   \qquad \Psi(p)=\frac{\cos(2\pi(p^2-p-1/16))}{\cos(2\pi p)}.$$
--
--   Write $R(t)$, $J(p)$, and $E_1(a,p)$ for the Riemann contour remainder, saddle
--   integral, and error integral defined in the accompanying Riemann–Siegel bundles.
--   Then
--
--   $$\begin{aligned}
--   &2\operatorname{Re}(e^{i\phi}R(t))-(-1)^{N+1}a^{-1/2}\Psi(p)\\
--   &=(-1)^{N+1}a^{-1/2}\bigl[
--   2\operatorname{Re}(e^{-\pi i/8}(e^{i(\phi-\theta_{\rm main})}-1)J(p))
--   +2\operatorname{Re}(e^{i(\phi-\theta_{\rm main}-\pi/8)}E_1(a,p))\bigr].
--   \end{aligned}$$
--
--   This isolates the error terms in the critical-line remainder.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_B3.lean#L255-L302

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_rsJ_C0
import Theorems.Thm_RSInt_rsRem_factor
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











/-! ## 3. The phase -/



/-! ## 4. The exact C0-corrected remainder -/

theorem RSInt.rs_remainder_exact {t : ℝ} (ht : 0 < t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) (φ : ℝ) :
    2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t) =
      (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) *
        (2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) * rsJ (rsFrac t)).re +
          2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 (rsAlpha t) (rsFrac t)).re) := by sorry
