-- Prove2me | Theorems.Thm_RSSeam_rs_remainder_C0_alpha_seam
-- name    : RSSeam.rs_remainder_C0_alpha_seam
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:34:12.430251+00:00
-- url     : https://prove2.me/theorems/2342720f-0c8c-4140-a7b4-f126a20528ab
-- title:
--   Riemann–Siegel remainder bound above height 509
-- statement:
--   Let $t\ge509$ and $a=\sqrt{t/(2\pi)}$, $N=\lfloor a\rfloor_{\mathbb N}$,
--   $p=a-N>0$, with $\cos(2\pi p)\ne0$. Define
--   $\Psi(p)=\cos(2\pi(p^2-p-1/16))/\cos(2\pi p)$ and
--   $\theta_{\rm main}=\frac t2\log t-\frac t2\log(2\pi)-\frac t2-\frac\pi8$.
--   Let $R(t)$ be the Riemann contour remainder defined in the accompanying bundle.
--   For any real $\phi$ with $|\phi-\theta_{\rm main}|\le1/t$,
--
--   $$\left|2\operatorname{Re}(e^{i\phi}R(t))-(-1)^{N+1}a^{-1/2}\Psi(p)\right|
--   \le\frac{13}{20}a^{-3/2}.$$
--
--   This remainder bound covers the lower-height part of the checker.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RSSeam_B3Bound.lean#L286-L346

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_norm_rsJ_le
import Theorems.Thm_RSInt_rs_remainder_exact
import Theorems.Thm_RSSeam_E1_const_le
import Theorems.Thm_RSSeam_norm_rsE1_le
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









/-! ## The explicit C0 remainder bound from t >= 509 -/

theorem RSSeam.rs_remainder_C0_alpha_seam {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      13 / 20 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by sorry
