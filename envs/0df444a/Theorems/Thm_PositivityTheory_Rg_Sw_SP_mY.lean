-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_mY
-- name    : PositivityTheory.Rg.Sw.SP.mY
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:03.288136+00:00
-- url     : https://prove2.me/theorems/7fc9402f-c221-46a8-b017-90e82e4aeb71
-- title:
--   SP: m Y
-- statement:
--   The SP construction uses the m Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeH.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeH.lean#L69-L73

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.mY (s : ℂ) (x v : MC n) (t : ℂ) :
    1 + (Complex.I * s) • Matrix.of (x + t • v) = (1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v) := by sorry
