-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_lift_PiJ
-- name    : PositivityTheory.Rg.Cz.PStepFormula.lift_PiJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:23.386557+00:00
-- url     : https://prove2.me/theorems/cd8b0d1e-a25d-446d-a842-f6aa9e285844
-- title:
--   PStep Formula: lift Pi J
-- statement:
--   The PStep Formula construction uses the lift Pi J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L35-L39

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

theorem PositivityTheory.Rg.Cz.PStepFormula.lift_PiJ {m : ℕ} {P : Type} (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (lift (PiJ m E u) : Module.End ℂ (TV n (TV n M (Fin m)) P)) =
      (List.ofFn fun i => algebraMap ℂ _ u + lift (xJ E i)).prod := by sorry
