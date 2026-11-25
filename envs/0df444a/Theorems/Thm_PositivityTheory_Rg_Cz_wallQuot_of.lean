-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_wallQuot_of
-- name    : PositivityTheory.Rg.Cz.wallQuot_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:51.23681+00:00
-- url     : https://prove2.me/theorems/122734bd-1f26-42f4-adf9-247871e7f3ad
-- title:
--   Cz: wall Quot of
-- statement:
--   The Cz construction uses the wall Quot of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallQuot.lean#L75-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallQuot.lean#L75-L121

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open WQ

theorem PositivityTheory.Rg.Cz.wallQuot_of (hQ : QdetFacts) : WallQuot := by sorry
