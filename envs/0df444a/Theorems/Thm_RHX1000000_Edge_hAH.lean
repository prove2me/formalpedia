-- Prove2me | Theorems.Thm_RHX1000000_Edge_hAH
-- name    : RHX1000000.Edge.hAH
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:13:02.443986+00:00
-- url     : https://prove2.me/theorems/568e86bd-17ad-4152-9f0c-fdaf8c5f4f1e
-- title:
--   Horizontal argument change of ζ at height 1000000
-- statement:
--   The horizontal argument change of $\zeta$ along $\sigma\in[2,-1]$ at height $t=10^6$ lies in the certified enclosure of the edge data:
--
--   $$
--   \Delta_{\sigma=2\to-1}\arg\zeta(\sigma+10^6\,i)\in[Lo,\,Hi].
--   $$
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunE00
import Definitions.Def_RHX1E6_RunE01
import Definitions.Def_RHX1E6_RunE02
import Definitions.Def_RHX1E6_RunE03
import Definitions.Def_RHX1E6_RunE04
import Definitions.Def_RHX1E6_RunE05
import Definitions.Def_RHX1E6_RunE06
import Definitions.Def_RHX1E6_RunE07
import Definitions.Def_RHX1E6_RunE08
import Definitions.Def_RHX1E6_RunE09
import Definitions.Def_RHX1E6_RunE10
import Definitions.Def_RHX1E6_RunE11
import Definitions.Def_RHX1E6_RunE12
import Definitions.Def_RHX1E6_RunE13
import Definitions.Def_RHX1E6_RunE14
import Definitions.Def_RHX1E6_RunE15
import Definitions.Def_RHX1E6_RunE16
import Definitions.Def_RHX1E6_RunE17
import Definitions.Def_RHX1E6_RunE18
import Definitions.Def_RHX1E6_RunE19
import Definitions.Def_RHX1E6_RunE20
import Definitions.Def_RHX1E6_RunE21
import Definitions.Def_RHX1E6_RunE22
import Definitions.Def_RHX1E6_RunE23
import Definitions.Def_RHX1E6_RunE24
import Definitions.Def_RHX1E6_RunE25
import Definitions.Def_RHX1E6_RunE26
import Definitions.Def_RHX1E6_RunE27
import Definitions.Def_RHX1E6_RunE28
import Definitions.Def_RHX1E6_RunE29
import Definitions.Def_RHX1E6_RunE30
import Definitions.Def_RHX1E6_RunE31
import Definitions.Def_RHX1E6_RunE32
import Definitions.Def_RHX1E6_RunE33
import Definitions.Def_RHX1E6_RunE34
import Definitions.Def_RHX1E6_RunE35
import Definitions.Def_RHX1E6_RunE36
import Definitions.Def_RHX1E6_RunE37
import Definitions.Def_RHX1E6_RunE38
import Definitions.Def_RHX1E6_RunE39
import Definitions.Def_RHX1E6_RunE40
import Definitions.Def_RHX1E6_RunE41
import Definitions.Def_RHX1E6_RunE42
import Definitions.Def_RHX1E6_RunE43
import Definitions.Def_RHX1E6_RunE44
import Definitions.Def_RHX1E6_RunE45
import Definitions.Def_RHX1E6_RunE46
import Definitions.Def_RHX1E6_RunE47
import Definitions.Def_RHX1E6_RunE48
import Definitions.Def_RHX1E6_RunE49
import Definitions.Def_RHX1E6_RunE50
import Definitions.Def_RHX1E6_RunE51
import Definitions.Def_RHX1E6_RunE52
import Definitions.Def_RHX1E6_RunE53
import Definitions.Def_RHX1E6_RunE54
import Definitions.Def_RHX1E6_RunE55
import Definitions.Def_RHX1E6_RunE56
import Definitions.Def_RHX1E6_RunE57
import Definitions.Def_RHX1E6_RunE58
import Definitions.Def_RHX1E6_RunE59
import Definitions.Def_RHX1E6_RunE60
import Definitions.Def_RHX1E6_RunE61
import Definitions.Def_RHX1E6_RunE62
import Definitions.Def_RHX1E6_RunE63
import Definitions.Def_RHX1E6_RunE64
import Definitions.Def_RHX1E6_RunE65
import Definitions.Def_RHX1E6_RunE66
import Definitions.Def_RHX1E6_RunE67
import Definitions.Def_RHX1E6_RunE68
import Definitions.Def_RHX1E6_RunE69
import Definitions.Def_RHX1E6_RunE70
import Definitions.Def_RHX1E6_RunE71
import Definitions.Def_RHX1E6_RunE72
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Arb4 Arb4.Q

theorem RHX1000000.Edge.hAH :
    DiffractionCore.argChangeHoriz riemannZeta (1000000 : ℝ) 2 (-1) ∈
      Set.Icc RHX1000000.Edge.E.Lo.val RHX1000000.Edge.E.Hi.val := by
  sorry
