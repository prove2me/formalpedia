-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_xJ_comm
-- name    : PositivityTheory.Rg.Cz.ChainP.xJ_comm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:15.705218+00:00
-- url     : https://prove2.me/theorems/df276bb3-a266-4a8a-a30a-f92ed730a402
-- title:
--   Chain P: x J comm
-- statement:
--   The Chain P construction uses the x J comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L73-L78

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

theorem PositivityTheory.Rg.Cz.ChainP.xJ_comm (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (m : ℕ) (j : Fin m)
    (a b : Fin n) : Commute (xJ E j) (tE (Finset.univ : Finset (Fin m)) E a b) := by sorry
