-- Prove2me | Theorems.Thm_RS5_lg_lo
-- name    : RS5.lg_lo
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:46:18.713528+00:00
-- url     : https://prove2.me/theorems/813c0d77-33e7-45dc-acb6-4261f9973a7d
-- title:
--   Lower logarithm bound from the fixed-point checker
-- statement:
--   Let $c$ be a valid evaluator configuration at real height $t$ and order $K$,
--   and let $z$ be a certificate satisfying the height-$509$ checker conditions
--   $\operatorname{Checks5}(c,z)$. Write $P$ for the precision of $c$, $N$ and
--   $L$ for the certificate fields $z.N$ and $z.LG0$, and
--   $p(t)=\sqrt{t/(2\pi)}-\lfloor\sqrt{t/(2\pi)}\rfloor_{\mathbb N}$.
--   Then, with the real division convention used by the definitions,
--
--   $$L\le2^P\log\!\left(1+\frac{p(t)}{N}\right).$$
--
--   This is the lower side of a certified logarithm enclosure.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS5_Sound.lean#L214-L247

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
import Theorems.Thm_RS4_log_one_add_near
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

theorem RS5.lg_lo (hv : Valid c t K) (hk : Checks5 c z) :
    (z.LG0 : ℝ) ≤ Real.log (1 + RSInt.rsFrac t / z.N) * 2 ^ c.P := by sorry
