-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_vM
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_vM
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:00:21.741051+00:00
-- url     : https://prove2.me/theorems/1d12ca27-48d0-4279-83a4-d7066bc59466
-- title:
--   B: dir C v M
-- statement:
--   The B construction uses the dir C v M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L252-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L252-L258

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.dirC_vM {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b k l : Fin n) :
    dirC (fun y => vM s y a b) (vkl k l) y = -(Complex.I * s * (vM s y a l * vM s y k b)) := by sorry
