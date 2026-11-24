-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_commute
-- name    : PositivityTheory.Rg.Cz.ChainP.listSub_commute
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:10.104122+00:00
-- url     : https://prove2.me/theorems/67044f8b-85ff-4d66-9c6c-c031c3069b90
-- title:
--   Chain P: list Sub commute
-- statement:
--   The Chain P construction uses the list Sub commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L66-L71

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

theorem PositivityTheory.Rg.Cz.ChainP.listSub_commute (A T : Module.End ℂ V) (h : Commute A T) (L : List ℂ) :
    Commute (L.map fun r => A - algebraMap ℂ _ r).prod T := by sorry
