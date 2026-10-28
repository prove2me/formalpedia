-- Prove2me | Theorems.Thm_RS5_check5_sound
-- name    : RS5.check5_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:48:36.939987+00:00
-- url     : https://prove2.me/theorems/bcb19b64-1e91-48b9-9be6-3dddbe5f3622
-- title:
--   Soundness of the height-509 Riemann–Siegel checker
-- statement:
--   Let $c$ be a valid fixed-point configuration at height $t$ and order $K$, with
--   precision $P$. Let $z$ be a certificate whose Boolean checker returns true,
--   and write $N,z_{\rm lo},z_{\rm hi}$ for its stored fields. Set
--   $a=\sqrt{t/(2\pi)}$, $p=a-\lfloor a\rfloor_{\mathbb N}$, and
--   $\theta_{\rm main}=\frac t2\log t-\frac t2\log(2\pi)-\frac t2-\frac\pi8$.
--   Let
--
--   $$Z_{\rm main}(t,\phi)=2\sum_{n=1}^{\lfloor a\rfloor}n^{-1/2}\cos(\phi-t\log n)
--   +(-1)^{\lfloor a\rfloor+1}\left(\frac{t}{2\pi}\right)^{-1/4}
--   \frac{\cos(2\pi(p^2-p-1/16))}{\cos(2\pi p)}.$$
--
--   Then $t\ge509$, $N=\lfloor a\rfloor_{\mathbb N}$, $p>0$, and $\cos(2\pi p)\ne0$.
--   For every real $\phi$ with $|\phi-\theta_{\rm main}|\le1/t$,
--
--   $$\frac{z_{\rm lo}}{2^{2P}}\le Z_{\rm main}(t,\phi)\le
--   \frac{z_{\rm hi}}{2^{2P}}.$$
--
--   This connects the finite integer checker to the real Riemann–Siegel main term.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS5_Sound.lean#L706-L753

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_cpow_term
import Theorems.Thm_ArbEcon_step_sound
import Theorems.Thm_ArbEcon_trig_sound
import Theorems.Thm_DIntvProd_DIntv_add_sound
import Theorems.Thm_RS4_log_one_add_near
import Theorems.Thm_RS5_lg_lo
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Trig
end ArbEcon.Trig
namespace ArbEcon.sgn
end ArbEcon.sgn
namespace DIntvProd
end DIntvProd
namespace DIntvProd.DIntv
end DIntvProd.DIntv
namespace RS4
end RS4
namespace RS4.Cert
end RS4.Cert
namespace RS4.Lser
end RS4.Lser
namespace RS4.negIf
end RS4.negIf
namespace RS4.sgnI
end RS4.sgnI
/-  RS5_Sound.lean -- lane B5: SOUNDNESS of the t >= 509 checker `RS5.check5`.

    This file is lane B4's `RS4_Sound` sections 1-9 (the checker's facts over the reals, the DIntv
    assembly and the soundness theorem) re-stated for `RS5.Checks5`, which differs from `RS4.Checks`
    ONLY in the height floor (`509 * 2^tq <= tn` instead of `10000 * 2^tq <= tn`).  The floor is used by
    exactly two facts, `t_ge` and `tn_pos`; every other proof is unchanged text.  The height-free
    helpers of `RS4_Sound` (`Zmain`, `Lser`, `log_one_add_near`, `lp_real`, `ballD_mem`, ...) and all
    computable definitions of `RS4_Eval` are REUSED (selective `open RS4 (...)`), not duplicated.

    ## The headline

      `RS5.check5_sound` : `Valid c t K` and `check5 c z = true` imply
        `509 <= t`, `rsNn t = z.N`, `0 < rsFrac t`, `cos (2 pi rsFrac t) ≠ 0`, and for EVERY phase
        `phi` with `|phi - rsThetaMain t| <= 1/t`:  `zlo / 2^(2P) <= RS4.Zmain t phi <= zhi / 2^(2P)`.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Real Finset
open ArbEcon DIntvProd
open RS4 (Cert lpPos lpNeg sgnI ballD negIf dstate phTrig mainBox c0Box zBox QuotOK Zmain Lser
  log_one_add_near      )

section
namespace RS5
end RS5
open RS5

noncomputable section

/-! ## 1. the checker's facts, over the reals -/

section Facts

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}























































/-! ## 2. the Dirichlet state: `psum t N` and `log N` -/







/-! ## 3. the phase ball -/











/-! ## 4. the C0 amplitude `(t/2pi)^(-1/4) = a^(-1/2)` -/









/-! ## 5. the angles `2 pi p` and `2 pi (p - p^2 + 1/16)` -/















end Facts

/-! ## 6. the quotient `Psi = cos v / cos 2 pi p` (denominator bounded away from 0) -/







/-! ## 7. the main sum as `Re (e^{i phi} psum t N)` -/



/-! ## 8. the DIntv assembly -/

section Assembly

variable {c : Cfg} {t : ℝ} {K : ℕ} {z : Cert}









end Assembly

/-! ## 9. THE SOUNDNESS THEOREM -/

theorem RS5.check5_sound {c : Cfg} {t : ℝ} {K : ℕ} (hv : Valid c t K) (z : Cert)
    (h : check5 c z = true) :
    509 ≤ t ∧ RSInt.rsNn t = z.N ∧ 0 < RSInt.rsFrac t ∧
      Real.cos (2 * π * RSInt.rsFrac t) ≠ 0 ∧
      ∀ φ : ℝ, |φ - RSInt.rsThetaMain t| ≤ 1 / t →
        (z.zlo : ℝ) / 2 ^ (2 * c.P) ≤ Zmain t φ ∧ Zmain t φ ≤ (z.zhi : ℝ) / 2 ^ (2 * c.P) := by sorry
