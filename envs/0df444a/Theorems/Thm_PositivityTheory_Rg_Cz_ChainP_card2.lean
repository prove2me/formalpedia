-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_card2
-- name    : PositivityTheory.Rg.Cz.ChainP.card2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:20.086002+00:00
-- url     : https://prove2.me/theorems/ef4ddb7c-9c88-4280-a9c0-5a19702f4e69
-- title:
--   Chain P: card2
-- statement:
--   The Chain P construction uses the card2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L47-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L47-L65

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

theorem PositivityTheory.Rg.Cz.ChainP.card2 {m : ℕ} (co : Fin (m + 1) → Fin n) :
    (Finset.univ.filter fun p : Fin (m + 1) => p < Fin.last m ∧ co p = co (Fin.last m)).card =
      (Finset.univ.filter fun p : Fin m => (co ∘ Fin.castSucc) p = co (Fin.last m)).card := by sorry
