-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_CGlue_pm_apply__c94cc9d97d61
-- name    : P2M_PositivityTheory_Rg_Cz_CGlue_pm_apply__c94cc9d97d61
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:20.426652+00:00
-- url     : https://prove2.me/theorems/5cbc615c-820b-5861-ad73-fe309ea0c429
-- title:
--   P2 M Positivity Theory Rg Cz CGlue pm apply  c94cc9d97d61: P2 M Positivity Theory Rg Cz CGlue pm apply  c94cc9d97d61
-- statement:
--   The P2 M Positivity Theory Rg Cz CGlue pm apply  c94cc9d97d61 construction uses the P2 M Positivity Theory Rg Cz CGlue pm apply  c94cc9d97d61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CoefficientGluing/SumFinVal.lean#L16-L17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CoefficientGluing_SumFinVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Formalism.REAL
open scoped TensorProduct
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CGlue
variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]

theorem P2M_PositivityTheory_Rg_Cz_CGlue_pm_apply__c94cc9d97d61 {M : Type} [AddCommGroup M] [Module ℂ M] (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) :
    pm σ f I = f (I ∘ σ) := by sorry

alias «PositivityTheory».«Rg».«Cz».«CGlue».«pm_apply'» := P2M_PositivityTheory_Rg_Cz_CGlue_pm_apply__c94cc9d97d61
