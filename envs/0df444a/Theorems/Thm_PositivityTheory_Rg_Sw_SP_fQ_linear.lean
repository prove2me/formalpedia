-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_fQ_linear
-- name    : PositivityTheory.Rg.Sw.SP.fQ_linear
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:47.952335+00:00
-- url     : https://prove2.me/theorems/da562fbe-3eb0-4330-abc4-f2cb34ead315
-- title:
--   SP: f Q linear
-- statement:
--   The SP construction uses the f Q linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L64-L68

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.fQ_linear (s z : ℂ) (m : ℕ) {ι : Type} (t : Finset ι) (a : ι → ℂ) (P : ι → Fm n) (B : MC n) :
    fQ s z m (∑ i ∈ t, a i • P i) B = ∑ i ∈ t, a i * fQ s z m (P i) B := by sorry
