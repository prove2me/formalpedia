-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_sum4
-- name    : PositivityTheory.Rg.Cz.sum4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:55.58324+00:00
-- url     : https://prove2.me/theorems/bbb3ca82-b870-4176-a4bc-194c47885d9f
-- title:
--   Cz: sum4
-- statement:
--   The Cz construction uses the sum4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L22-L30

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

theorem PositivityTheory.Rg.Cz.sum4 {α β : Type} (s : Finset α) (t : Finset β) (F : Fin n → Fin n → α → β → ℂ) :
    ∑ a, ∑ c, ∑ p ∈ s, ∑ q ∈ t, F a c p q = ∑ p ∈ s, ∑ q ∈ t, ∑ a, ∑ c, F a c p q := by sorry
