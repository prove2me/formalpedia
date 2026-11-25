-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_app_upd_l
-- name    : PositivityTheory.Rg.Cz.PStepFormula.app_upd_l
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:58.601834+00:00
-- url     : https://prove2.me/theorems/f783aa79-c232-45eb-8483-76c30d97820a
-- title:
--   PStep Formula: app upd l
-- statement:
--   The PStep Formula construction uses the app upd l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L58-L67

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

theorem PositivityTheory.Rg.Cz.PStepFormula.app_upd_l {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (i : Fin m) (a : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) a = Fin.append (Function.update I i a) J := by sorry
