-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_colAnti_of
-- name    : PositivityTheory.Rg.Cz.colAnti_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:01.238801+00:00
-- url     : https://prove2.me/theorems/07c6bfbb-9f6a-4b83-abbd-aa8362e4135e
-- title:
--   Cz: col Anti of
-- statement:
--   The Cz construction uses the col Anti of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L133-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PColAnti.lean#L133-L205

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
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
open ColumnAntisymmetry

theorem PositivityTheory.Rg.Cz.colAnti_of : TensorGl → JMComm → Height → ColAnti := by sorry
