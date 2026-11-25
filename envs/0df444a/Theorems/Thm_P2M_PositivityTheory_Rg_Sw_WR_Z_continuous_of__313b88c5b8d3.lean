-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_Z_continuous_of__313b88c5b8d3
-- name    : P2M_PositivityTheory_Rg_Sw_WR_Z_continuous_of__313b88c5b8d3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:55.767555+00:00
-- url     : https://prove2.me/theorems/74f802e2-3658-4464-b472-e2623c8c9758
-- title:
--   P2 M Positivity Theory Rg Sw WR Z continuous of  313b88c5b8d3: P2 M Positivity Theory Rg Sw WR Z continuous of  313b88c5b8d3
-- statement:
--   The P2 M Positivity Theory Rg Sw WR Z continuous of  313b88c5b8d3 construction uses the P2 M Positivity Theory Rg Sw WR Z continuous of  313b88c5b8d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L87-L88

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_WR_Z_continuous_of__313b88c5b8d3 : Continuous fun B : MC n => Matrix.of B := by sorry

alias «PositivityTheory».«Rg».«Sw».«WR».«Z».«continuous_of'» := P2M_PositivityTheory_Rg_Sw_WR_Z_continuous_of__313b88c5b8d3
