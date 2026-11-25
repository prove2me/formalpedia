-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_contract_of
-- name    : PositivityTheory.Rg.Cz.contract_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:45.663807+00:00
-- url     : https://prove2.me/theorems/e32e0e75-c05b-5e1d-a685-be2db625eb75
-- title:
--   Cz: contract of
-- statement:
--   The Cz construction uses the contract of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContract.lean#L11-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContract.lean#L11-L102

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContract
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
open CtrX

theorem PositivityTheory.Rg.Cz.contract_of : TensorGl → QdetFacts → WallAlg → TensorGK → LieInv → WallQuot → Contract := by sorry
