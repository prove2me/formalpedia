-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_stepFormula_of
-- name    : PositivityTheory.Rg.Cz.stepFormula_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:14.772876+00:00
-- url     : https://prove2.me/theorems/f7512161-d84f-48f6-981d-0c97b1860cd1
-- title:
--   Cz: step Formula of
-- statement:
--   The Cz construction uses the step Formula of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormula.lean#L101-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormula.lean#L101-L135

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormula
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
open PStepFormula

theorem PositivityTheory.Rg.Cz.stepFormula_of : TensorGl → JMComm → PiQdet → Curry → StepFormula := by sorry
