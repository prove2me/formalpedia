-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_pm_apply__4f09274ebe81
-- name    : P2M_PositivityTheory_Rg_Cz_pm_apply__4f09274ebe81
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:27.645925+00:00
-- url     : https://prove2.me/theorems/60bf451e-be9b-49ef-9cfb-aec7c4021c68
-- title:
--   P2 M Positivity Theory Rg Cz pm apply  4f09274ebe81: P2 M Positivity Theory Rg Cz pm apply  4f09274ebe81
-- statement:
--   The P2 M Positivity Theory Rg Cz pm apply  4f09274ebe81 construction uses the P2 M Positivity Theory Rg Cz pm apply  4f09274ebe81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L12-L13

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem P2M_PositivityTheory_Rg_Cz_pm_apply__4f09274ebe81 (σ : Equiv.Perm Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ σ) := by sorry

alias «PositivityTheory».«Rg».«Cz».«pm_apply'» := P2M_PositivityTheory_Rg_Cz_pm_apply__4f09274ebe81
