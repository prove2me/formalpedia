-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_tE_zero_apply
-- name    : PositivityTheory.Rg.Cz.tE_zero_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:26.559694+00:00
-- url     : https://prove2.me/theorems/084d1df1-c04a-45f5-9c33-e2ea71569847
-- title:
--   Cz: t E zero apply
-- statement:
--   The Cz construction uses the t E zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L17-L20

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_Expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem PositivityTheory.Rg.Cz.tE_zero_apply (S : Finset Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) f I =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I := by sorry
