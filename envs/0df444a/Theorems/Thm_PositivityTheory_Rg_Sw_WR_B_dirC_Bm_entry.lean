-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_Bm_entry
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_Bm_entry
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:39.536601+00:00
-- url     : https://prove2.me/theorems/5a77bc42-9c33-5c70-887a-862529e25127
-- title:
--   B: dir C Bm entry
-- statement:
--   The B construction uses the dir C Bm entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L226-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L226-L234

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

theorem PositivityTheory.Rg.Sw.WR.B.dirC_Bm_entry (s : ℂ) (y : E n) (a b k l : Fin n) :
    dirC (fun y => Bm s y a b) (vkl k l) y = Complex.I * s * Matrix.single l k (1 : ℂ) a b := by sorry
