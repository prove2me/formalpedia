-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_line_fQ
-- name    : PositivityTheory.Rg.Sw.SP.line_fQ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:00.445094+00:00
-- url     : https://prove2.me/theorems/9997d365-0111-4e43-ab6c-476ca178012b
-- title:
--   SP: line f Q
-- statement:
--   The SP construction uses the line f Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L42-L58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
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

theorem PositivityTheory.Rg.Sw.SP.line_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) :
    HasDerivAt (fun t : ℂ => fQ s z m Q (x + t • eU k l)) (fQ s z m (opD s m k l Q) x) 0 := by sorry
