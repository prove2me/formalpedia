-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_card3
-- name    : PositivityTheory.Rg.Cz.ChainP.card3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:23.35869+00:00
-- url     : https://prove2.me/theorems/440e541c-cefd-412a-849a-07a474a1571a
-- title:
--   Chain P: card3
-- statement:
--   The Chain P construction uses the card3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L67-L71

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
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
open PositivityTheory.Rg.Cz.ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.ChainP.card3 {m : ℕ} (co : Fin (m + 1) → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : Fin (m + 1) => co p = k).card =
      (Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = k).card + if co (Fin.last m) = k then 1 else 0 := by sorry
