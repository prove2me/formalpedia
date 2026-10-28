-- Prove2me | Theorems.Thm_RSInt_norm_E1_integrand_near_prime
-- name    : RSInt.norm_E1_integrand_near_prime
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:08:08.989161+00:00
-- url     : https://prove2.me/theorems/302e5e12-04f8-401c-9309-99c5521d71fb
-- title:
--   A refined near-saddle integrand bound
-- statement:
--   Let $a_0,a,p,v$ be real, with $9\le a_0\le a$ and $|v|\le a/3$. Put
--   $w=v(1+i)$, $D(z)=e^{\pi iz}-e^{-\pi iz}$, and
--   $\Phi_a(w)=e^{2\pi iaw-\pi iw^2}(1+w/a)^{-1/2-2\pi ia^2}$, using the principal
--   complex power and the formal convention $1/0=0$. For the coefficient functions $c_{\rm main}$, $c_{\rm two}$,
--   and $c_S$ defined in the accompanying bounds,
--
--   $$\begin{aligned}
--   &\left|\frac{e^{2\pi iw^2}}{D(p+w)}(\Phi_a(w)-1)(1+i)\right|\\
--   &\le\frac{e^{-4\pi v^2}}{2\pi a}\sum_{j=0}^{4}c_{\rm main}(j)|v|^j
--   +\frac{\sqrt2 e^{-4\pi v^2}}{2\pi a^2}\sum_{j=0}^{3}c_{\rm two}(j)|v|^j\\
--   &\quad+\frac{\sqrt2 e^{1/(2a_0^2)}e^{-(4\pi-37/10)v^2}}{2\pi a^2}
--   \sum_{j=0}^{7}c_S(a_0,j)|v|^j.
--   \end{aligned}$$
--
--   This provides a pointwise majorant for the near-saddle remainder integral.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_B3Sharp.lean#L466-L560

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_B3Sharp
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_near_eta_le_lin
import Theorems.Thm_RSInt_near_eta_le_sq
import Theorems.Thm_RSInt_norm_rsPhi_sub_one_le_prime
import Theorems.Thm_RSInt_rsEone_line
namespace RSInt
end RSInt
/-  RS_B3Sharp.lean -- lane RS, brick B3 SHARPENED (RSC0 Phase 2): the same C0-corrected
    Riemann-Siegel remainder as `RS_B3Bound` / `RSSeam_B3Bound`, with smaller kernel-checked constants.
    New theorems only; imports `RSSeam_B3Bound` (hence `RS_B3Bound`) read-only and edits nothing.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_remainder_C0_alpha'` : for t >= 4250 (a = sqrt(t/2pi) >= 26), 0 < p = rsFrac t,
      cos(2 pi p) ≠ 0, and every phase phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (3/20) a^(-3/2);
      `RSInt.rs_remainder_C0'` : the same in t, <= (3/5) t^(-3/4).
      `RSSeam.rs_remainder_C0_alpha_seam'` : for t >= 509, <= (21/100) a^(-3/2);
      `RSSeam.rs_remainder_C0_seam'` : the same in t, <= (21/25) t^(-3/4).
      The old statements (2/5 and 2 at t >= 10000; 13/20 and 13/5 at t >= 509) are re-derived from
      the new ones as `*_of_sharp` corollaries at the end of the file.

    ## What is sharper than `RS_B3Bound` (same architecture, elementary steps)

      * the saddle exponent E is split as E = E1 + E2 with E1 = -2 pi i w^3/(3a) - w/(2a) EXACT and
        |E2| <= pi |w|^4/a^2 + |w|^2/(2a^2) (Mathlib's log-Taylor remainders of orders 4 and 2), and
        |e^E - 1| <= |E| + |E|^2 e^{|E|} (`norm_rsPhi_sub_one_le'`);
      * on the steepest-descent line |E1| = (sqrt2/2)|v| |1 - 8 pi v^2/3| / a EXACTLY (`rsEone_line`):
        the linear and cubic terms have OPPOSITE signs, and |1 - x| <= 41/40 - (5/4)x + (5/8)x^2;
        the main term then integrates against the FULL Gaussian e^{-4 pi v^2} to (49/120)/(2 pi a);
      * only the second-order remainder pays for e^{|E|}, with e^{-(4 pi - 37/10) v^2};
      * absolute Gaussian moments int |v|^j e^{-b v^2} = b^{-(j+1)/2} Gamma((j+1)/2) (`gaussMom_eq`);
      * one near-zone lemma (|v| <= a/3) for every a >= a0 >= 9, the far zone reused verbatim from
        `RSSeam.norm_E1_integrand_far`;
      * |rsJ p| <= 4/5 by completing the square on the midline (was 4) (`norm_rsJ_le'`).
      Budget: |rsE1| <= (7/100)/a (a >= 26) and (9/100)/a (a >= 9); phase 4/(5 pi a^2) <= (1/100)/a
      resp. (3/100)/a; 2 (7/100) + 1/100 = 3/20 and 2 (9/100) + 3/100 = 21/100; (2 pi)^(3/4) <= 4.

    The numeric lemmas bound a|rsE1| by 0.0689 (a >= 26) and 0.0821 (a >= 9).  Untrusted design
    numerics (closed forms 0.0688 and 0.0770): ~/rh-team/rsc0/out/phase2/lean_numerics.py.

    Not yet `lean_lib`s (lakefile.toml untouched): compile with `lake env lean`; a landing PR adds
    append-only `[[lean_lib]]` entries for RS_B3Sharp and RS_BridgeSharp (and RS_AxiomGuardSharp).

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Absolute Gaussian moments -/





































/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/











/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/

theorem RSInt.norm_E1_integrand_near_prime {a0 a p v : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) (hv : |v| ≤ a / 3) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      1 / (2 * π * a) *
          ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
        Real.sqrt 2 / (2 * π * a ^ 2) *
          ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
        Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
          ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by sorry
