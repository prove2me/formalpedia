-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_rot_nat
-- name    : PositivityTheory.Rg.Cz.PStepFormula.rot_nat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:38.813792+00:00
-- url     : https://prove2.me/theorems/aa511944-b554-4137-91b1-c18d570edd09
-- title:
--   PStep Formula: rot nat
-- statement:
--   The PStep Formula construction uses the rot nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L156-L157

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

theorem PositivityTheory.Rg.Cz.PStepFormula.rot_nat (i : Fin n) (h : (i : ℕ) < 1 + n) : rot n ⟨i, h⟩ = Fin.natAdd 1 i := by sorry
