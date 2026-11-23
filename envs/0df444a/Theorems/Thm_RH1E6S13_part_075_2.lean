-- Prove2me | Theorems.Thm_RH1E6S13_part_075_2
-- name    : RH1E6S13.part_075_2
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:20:54.233007+00:00
-- url     : https://prove2.me/theorems/d78c2fe1-d20f-4d6b-8c9a-3f22a2ba334e
-- title:
--   Zeros of ζ on the critical line, segment 13, group 075, part 2 (heights ≈791134.9207–≈791270.8204)
-- statement:
--   The sample data `RH1E6S13_D075_2` give 254 zeros of $\zeta(1/2+it)$, counted by sign changes of Hardy's $Z(t)$, with $t\in[≈791134.9207,\,≈791270.8204]$:
--
--   $$
--   \texttt{RS5.BandZeros}\ t_{\mathrm{first}}\ t_{\mathrm{last}}\ 254.
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

namespace RH1E6S13

theorem part_075_2 : RS5.BandZeros ((51847818160 : ℝ) / 65536) ((51856724484 : ℝ) / 65536) 254 := by
  sorry

end RH1E6S13
