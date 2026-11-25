-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_transFin_of
-- name    : PositivityTheory.Rg.Cz.transFin_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:20.619371+00:00
-- url     : https://prove2.me/theorems/69c8cb32-c8bb-4315-834d-caf54698a6fc
-- title:
--   Cz: trans Fin of
-- statement:
--   The Cz construction uses the trans Fin of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFin.lean#L41-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFin.lean#L41-L278

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin
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

theorem PositivityTheory.Rg.Cz.transFin_of : TensorGl → JMComm → StepFormula → QdetFacts → Spectrum → Chain → ColAnti → TransFin := by sorry
