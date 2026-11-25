-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_lieInv_holds
-- name    : PositivityTheory.Rg.Cz.lieInv_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:00.297562+00:00
-- url     : https://prove2.me/theorems/c1080f91-4217-5427-adfb-146ef9ac1225
-- title:
--   Cz: lie Inv holds
-- statement:
--   The Cz construction uses the lie Inv holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PLieInv.lean#L73-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PLieInv.lean#L73-L166

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open LieInverse

theorem PositivityTheory.Rg.Cz.lieInv_holds : LieInv := by sorry
