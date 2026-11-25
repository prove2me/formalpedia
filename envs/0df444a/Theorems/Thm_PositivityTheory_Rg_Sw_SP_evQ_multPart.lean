-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_multPart
-- name    : PositivityTheory.Rg.Sw.SP.evQ_multPart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:27.957723+00:00
-- url     : https://prove2.me/theorems/5b5b8cbd-9837-4035-8a8a-d00ac21c97a4
-- title:
--   SP: ev Q mult Part
-- statement:
--   The SP construction uses the ev Q mult Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeB.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeB.lean#L33-L35

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

theorem PositivityTheory.Rg.Sw.SP.evQ_multPart (s z : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (multPart s m b k l Q) B = -(cB s b) * ((alB m b).eval z * vals s B (b, l, k) * evQ s z Q B) := by sorry
