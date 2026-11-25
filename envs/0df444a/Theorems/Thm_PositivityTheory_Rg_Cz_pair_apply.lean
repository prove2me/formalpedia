-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_pair_apply
-- name    : PositivityTheory.Rg.Cz.pair_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:31.474681+00:00
-- url     : https://prove2.me/theorems/4542cb8f-6446-56b0-b217-412f67e622de
-- title:
--   Cz: pair apply
-- statement:
--   The Cz construction uses the pair apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L32-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L32-L55

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

theorem PositivityTheory.Rg.Cz.pair_apply (p q : Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    ∑ a, ∑ c, (eAt p a c : Module.End ℂ (TV n ℂ Q)) ((eAt q c a : Module.End ℂ (TV n ℂ Q)) f) I =
      if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q) := by sorry
