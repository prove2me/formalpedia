-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_height_of
-- name    : PositivityTheory.Rg.Cz.height_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:06.392042+00:00
-- url     : https://prove2.me/theorems/b66f3580-264e-4a16-989e-5c9643a9a1bb
-- title:
--   Cz: height of
-- statement:
--   The Cz construction uses the height of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L350-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L350-L385

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
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
open HeightVanishing

theorem PositivityTheory.Rg.Cz.height_of : TensorGl → Height := by sorry
