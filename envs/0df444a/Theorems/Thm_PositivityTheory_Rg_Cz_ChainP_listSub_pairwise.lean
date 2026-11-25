-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_pairwise
-- name    : PositivityTheory.Rg.Cz.ChainP.listSub_pairwise
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:49:02.09184+00:00
-- url     : https://prove2.me/theorems/9afe6369-2a6b-41b5-a9d9-a7827c102293
-- title:
--   Chain P: list Sub pairwise
-- statement:
--   The Chain P construction uses the list Sub pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L73-L77

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
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
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem PositivityTheory.Rg.Cz.ChainP.listSub_pairwise (A : Module.End ℂ V) (L : List ℂ) :
    (L.map fun r => A - algebraMap ℂ _ r).Pairwise Commute := by sorry
