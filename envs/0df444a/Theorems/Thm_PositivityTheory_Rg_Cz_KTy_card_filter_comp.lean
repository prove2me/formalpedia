-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_KTy_card_filter_comp
-- name    : PositivityTheory.Rg.Cz.KTy.card_filter_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:00.98383+00:00
-- url     : https://prove2.me/theorems/f329d15d-7e26-4450-a2de-df9421a984a6
-- title:
--   KTy: card filter comp
-- statement:
--   The KTy construction uses the card filter comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PKTypeA.lean#L24-L27

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

theorem PositivityTheory.Rg.Cz.KTy.card_filter_comp {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → Prop) [DecidablePred f] :
    (Finset.univ.filter fun a => f (e a)).card = (Finset.univ.filter f).card := by sorry
