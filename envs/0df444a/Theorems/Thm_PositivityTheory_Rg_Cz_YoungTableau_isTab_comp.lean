-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_isTab_comp
-- name    : PositivityTheory.Rg.Cz.YoungTableau.isTab_comp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:22.615809+00:00
-- url     : https://prove2.me/theorems/62886d4c-f49d-4e80-af6d-6a062bed33d0
-- title:
--   Young Tableau: is Tab comp
-- statement:
--   The Young Tableau construction uses the is Tab comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L246-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PYoungA.lean#L246-L253

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]

theorem PositivityTheory.Rg.Cz.YoungTableau.isTab_comp {Y : Type} (col : X → C) (b : X → Fin n) (hT : IsTab col b) (e : Y → X)
    (he : Function.Injective e) (hcl : ∀ q y, col q = col (e y) → ∃ y', q = e y') : IsTab (col ∘ e) (b ∘ e) := by sorry
