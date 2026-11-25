-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_card_filter_sum
-- name    : PositivityTheory.Rg.Cz.KTy.card_filter_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:17.04307+00:00
-- url     : https://prove2.me/theorems/6626d08f-2bd8-45a7-9e31-0497078e6637
-- title:
--   KTy: card filter sum
-- statement:
--   The KTy construction uses the card filter sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L29-L32

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
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
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (nu : ι → Fin n → ℕ) (H : Finset ι)

theorem PositivityTheory.Rg.Cz.KTy.card_filter_sum {α β : Type} [Fintype α] [Fintype β] (f : α ⊕ β → Prop) [DecidablePred f] :
    (Finset.univ.filter f).card =
      (Finset.univ.filter fun a => f (.inl a)).card + (Finset.univ.filter fun b => f (.inr b)).card := by sorry
