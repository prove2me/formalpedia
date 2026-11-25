-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_dot_pm_swap
-- name    : PositivityTheory.Rg.Cz.dot_pm_swap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:56:16.701654+00:00
-- url     : https://prove2.me/theorems/68ba2f10-b4aa-5979-81c0-1e1e503bcb9d
-- title:
--   Cz: dot pm swap
-- statement:
--   The Cz construction uses the dot pm swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L18-L27

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

theorem PositivityTheory.Rg.Cz.dot_pm_swap (a c : Q) (u v : TV n ℂ Q) :
    star u ⬝ᵥ (pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) v =
      star ((pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) u) ⬝ᵥ v := by sorry
