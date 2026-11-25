-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_card1
-- name    : PositivityTheory.Rg.Cz.ChainP.card1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:31.389802+00:00
-- url     : https://prove2.me/theorems/be76315f-2fd5-42a0-8a36-f2ccbb3004e7
-- title:
--   Chain P: card1
-- statement:
--   The Chain P construction uses the card1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L23-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L23-L45

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

theorem PositivityTheory.Rg.Cz.ChainP.card1 {m : ℕ} (co : Fin (m + 1) → Fin n) (i : Fin m) :
    (Finset.univ.filter fun p : Fin (m + 1) => p < i.castSucc ∧ co p = co i.castSucc).card =
      (Finset.univ.filter fun p : Fin m => p < i ∧ (co ∘ Fin.castSucc) p = (co ∘ Fin.castSucc) i).card := by sorry
