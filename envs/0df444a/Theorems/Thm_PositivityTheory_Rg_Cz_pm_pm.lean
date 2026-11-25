-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_pm_pm
-- name    : PositivityTheory.Rg.Cz.pm_pm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:43.116272+00:00
-- url     : https://prove2.me/theorems/7cf4e2fd-09ef-5dbd-a2a7-11f2867074ef
-- title:
--   Cz: pm pm
-- statement:
--   The Cz construction uses the pm pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L15-L16

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

theorem PositivityTheory.Rg.Cz.pm_pm (σ τ : Equiv.Perm Q) (f : TV n ℂ Q) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) (pm τ f) = pm (σ * τ) f := by sorry
