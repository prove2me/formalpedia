-- Prove2me | Theorems.Thm_RSSeam_norm_rsE1_le
-- name    : RSSeam.norm_rsE1_le
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:22:28.944522+00:00
-- url     : https://prove2.me/theorems/b2c1ea7c-ce87-4b0b-9f39-460994e774fd
-- title:
--   An explicit bound for the saddle remainder at the seam
-- statement:
--   Let $a\ge9$ and $p$ be real. Put $w=v(1+i)$,
--   $D(z)=e^{\pi iz}-e^{-\pi iz}$,
--   $\Phi_a(w)=e^{2\pi iaw-\pi iw^2}(1+w/a)^{-1/2-2\pi ia^2}$, and
--
--   $$E_1(a,p)=\int_{\mathbb R}\frac{e^{2\pi iw^2}(\Phi_a(w)-1)}{D(p+w)}(1+i)\,dv.$$
--
--   Using the principal complex power and the formal division convention at zero,
--
--   $$|E_1(a,p)|\le\frac{e^{1/600}}{\pi a}\frac{13}{25}\sqrt{\frac\pi7}
--   +\frac{e^{1/600}}{\pi a}\frac{17}{2}\frac{\sqrt{\pi/7}}{14}
--   +5e^{-\pi a^2/18}\sqrt{\frac{\pi}{\pi/2}}.$$
--
--   This is the integrated remainder estimate used at the seam.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RSSeam_B3Bound.lean#L170-L218

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integral_sq_mul_exp_neg_mul_sq
import Theorems.Thm_RSSeam_norm_E1_integrand_far
import Theorems.Thm_RSSeam_norm_E1_integrand_near
namespace RSInt
end RSInt
/-  RSSeam_B3Bound.lean -- lane SEAM: the C0-corrected Riemann-Siegel remainder bound with a LOWER
    starting height, t >= 509 (saddle variable a = sqrt(t/2pi) >= 9) instead of t >= 10000 (a >= 39).
    Imports `RS_B3Bound` read-only and reuses its lemmas; nothing in lane RS is edited.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `rs_remainder_C0_alpha_seam` : for t >= 509, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, and every phase
      phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (13/20) a^(-3/2).
      `rs_remainder_C0_seam` : the same in t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (13/5) t^(-3/4).

    ## What changed against `RS_B3Bound` (the error budget re-run at a >= 9)

      * near/far split of the error integral at |v| = a/3 (was a/9); near the saddle the amplitude
        bound |rsPhi - 1| <= e e^e still applies because |w| = sqrt 2 |v| <= a/2;
      * near: e <= |w| (13/25 + 17/4 |w|^2)/a and e <= 27/5 v^2 + 1/600, so the integrand is
        <= e^{1/600}/(pi a) (13/25 + 17/2 v^2) e^{-7 v^2};
      * far: |integrand| <= 5 e^{-pi a^2/18} e^{-pi v^2/2}, and e^{-x} <= 8!/x^8 at x >= 14;
      * |rsE1 a p| <= (49/200 + 1/200)/a = (1/4)/a for a >= 9 (was (9/50)/a for a >= 39);
      * |rsJ p| <= 4 (unchanged, `RSInt.norm_rsJ_le`); phase term 8|delta| <= 4/(pi a^2) <= (3/20)/a;
      * budget 2 (1/4) + 3/20 = 13/20 in the a-form; (2 pi)^(3/4) <= 4 gives 13/5 in t.

    Untrusted numerics (scratchpad/seam/remainder.py): the true C0-corrected remainder is
    <= 0.121 t^(-3/4) on samples in [200, 10100]; so 13/5 is honest with a ~20x margin.

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSSeam
end RSSeam
open RSSeam

open RSInt

theorem RSSeam.norm_rsE1_le {a p : ℝ} (ha : 9 ≤ a) :
    ‖rsE1 a p‖ ≤ Real.exp (1 / 600) / (π * a) * (13 / 25) * Real.sqrt (π / 7) +
      Real.exp (1 / 600) / (π * a) * (17 / 2) * (Real.sqrt (π / 7) / (2 * 7)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) := by sorry
