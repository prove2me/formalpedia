-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_chain_of
-- name    : PositivityTheory.Rg.Cz.chain_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:37.489393+00:00
-- url     : https://prove2.me/theorems/e54444ee-1aeb-4993-92b8-9c5e6e6ec7d2
-- title:
--   Cz: chain of
-- statement:
--   The Cz construction uses the chain of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L418-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChain.lean#L418-L425

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

theorem PositivityTheory.Rg.Cz.chain_of : TensorGl → JMComm → Curry → StepFormula → QdetFacts → StepChar → Height → WallQuot →
    Chain := by sorry
