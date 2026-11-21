-- Prove2me | Theorems.Thm_RH1E6S05_part_086_0
-- name    : RH1E6S05.part_086_0
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:10:53.504173+00:00
-- url     : https://prove2.me/theorems/839d601c-90f0-41dd-919c-64cf3fad9b29
-- title:
--   Zeros of ζ on the critical line, segment 05, group 086, part 0 (heights ≈399927.6614–400000)
-- statement:
--   The sample data `RH1E6S05_D086_0` give 128 zeros of $\zeta(1/2+it)$, counted by sign changes of Hardy's $Z(t)$, with $t\in[≈399927.6614,\,400000]$:
--
--   $$
--   \texttt{RS5.BandZeros}\ t_{\mathrm{first}}\ t_{\mathrm{last}}\ 128.
--   $$
--
--   `RS5.BandZeros a b K` is the framework's statement that there are $K$ increasing ordinates in $[a,b]$ at which $\zeta(1/2+it)$ vanishes.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Band
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS5_Z
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_B3Sharp
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_BandSharp
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem part_086_0 : RS5.BandZeros ((26209659216 : ℝ) / 65536) ((26214400000 : ℝ) / 65536) 128 := by
  sorry

end RH1E6S05
