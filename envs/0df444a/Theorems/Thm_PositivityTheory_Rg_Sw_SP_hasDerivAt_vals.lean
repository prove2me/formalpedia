-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_hasDerivAt_vals
-- name    : PositivityTheory.Rg.Sw.SP.hasDerivAt_vals
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:00:19.032815+00:00
-- url     : https://prove2.me/theorems/07bf5b66-e9e1-45fa-ab74-4d44a8d9ef44
-- title:
--   SP: has Deriv At vals
-- statement:
--   The SP construction uses the has Deriv At vals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L18-L23

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

theorem PositivityTheory.Rg.Sw.SP.hasDerivAt_vals (s : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (kk : Bool × Fin n × Fin n) :
    HasDerivAt (fun t : ℂ => vals s (x + t • eU k l) kk) (gD s x k l kk) 0 := by sorry
