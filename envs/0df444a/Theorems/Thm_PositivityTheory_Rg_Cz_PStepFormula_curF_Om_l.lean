-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_curF_Om_l
-- name    : PositivityTheory.Rg.Cz.PStepFormula.curF_Om_l
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:35.231309+00:00
-- url     : https://prove2.me/theorems/3ff0aa4d-d4a3-40cc-81f6-3b66940f876c
-- title:
--   PStep Formula: cur F Om l
-- statement:
--   The PStep Formula construction uses the cur F Om l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L76-L79

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
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
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.PStepFormula.curF_Om_l {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (i : Fin m) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.castAdd k i) f) = lift (Om E i) (curF n M m k f) := by sorry
