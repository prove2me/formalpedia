-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_trace_eU
-- name    : PositivityTheory.Rg.Sw.SP.trace_eU
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:22.811375+00:00
-- url     : https://prove2.me/theorems/d85edf42-8db3-5041-b094-87ce574b3f01
-- title:
--   SP: trace e U
-- statement:
--   The SP construction uses the trace e U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeB.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeB.lean#L46-L57

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
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

theorem PositivityTheory.Rg.Sw.SP.trace_eU (Y : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (Y * Matrix.of (eU k l)).trace = Y l k := by sorry
