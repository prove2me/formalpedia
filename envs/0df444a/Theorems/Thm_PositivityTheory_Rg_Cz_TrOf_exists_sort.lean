-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_exists_sort
-- name    : PositivityTheory.Rg.Cz.TrOf.exists_sort
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:49:22.545637+00:00
-- url     : https://prove2.me/theorems/0c88d731-bf7d-40d9-b36b-fb32fb7e8438
-- title:
--   Tr Of: exists sort
-- statement:
--   The Tr Of construction uses the exists sort property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L144-L147

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
omit [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TrOf.exists_sort {α : Type} [LinearOrder α] (key : P → α) :
    ∃ e : P ≃ Fin (Fintype.card P), Monotone (key ∘ e.symm) := by sorry
