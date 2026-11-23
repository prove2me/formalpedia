-- Prove2me | Theorems.Thm_RH1E6S13_seg
-- name    : RH1E6S13.seg
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:21:00.381463+00:00
-- url     : https://prove2.me/theorems/5a4b9b46-ec67-4f26-a7d7-7795dddc75ea
-- title:
--   93285 zeros of ζ on the critical line between heights 750000 and 800000
-- statement:
--   Segment 13 of the extension from $100000$ to $10^6$: $\texttt{RS5.BandZeros}\ 750000\ 800000\ 93285$, that is, 93285 increasing ordinates $t\in[750000,\,800000]$ with $\zeta(1/2+it)=0$.
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

theorem RH1E6S13.seg : RS5.BandZeros ((49152000000 : ℝ) / 65536) ((52428800000 : ℝ) / 65536) 93285 := by
  sorry
