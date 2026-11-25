-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_app_swap
-- name    : PositivityTheory.Rg.Cz.PStepFormula.app_swap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:29.13625+00:00
-- url     : https://prove2.me/theorems/ca640860-6b27-4d7f-961f-4e5984efa678
-- title:
--   PStep Formula: app swap
-- statement:
--   The PStep Formula construction uses the app swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L177-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L177-L192

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

theorem PositivityTheory.Rg.Cz.PStepFormula.app_swap (I : Fin 1 → Fin n) (J : Fin n → Fin n) (j : Fin n) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0) =
      Fin.append (Function.update I 0 (J j)) (Function.update J j (I 0)) := by sorry
