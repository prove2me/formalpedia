-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_count_up
-- name    : PositivityTheory.Rg.Cz.count_up
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:02.376466+00:00
-- url     : https://prove2.me/theorems/d1aa41cc-b622-4528-a956-669625a7bcbd
-- title:
--   Cz: count up
-- statement:
--   The Cz construction uses the count up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/CountSame.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/CountSame.lean#L22-L44

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_CountSame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] {C : Type} [DecidableEq C] {col : Q → C}
  {b : Q → Fin n} {S : Finset Q}

theorem PositivityTheory.Rg.Cz.count_up (hT : IsTab col b) (hS : ∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) (p : Q) (hp : p ∈ S) :
    ((S.filter fun q => col q = col p ∧ b p < b q).card : ℝ) = n - 1 - (b p : ℕ) := by sorry
