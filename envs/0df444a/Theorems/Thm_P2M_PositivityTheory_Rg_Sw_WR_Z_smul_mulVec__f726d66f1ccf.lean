-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_Z_smul_mulVec__f726d66f1ccf
-- name    : P2M_PositivityTheory_Rg_Sw_WR_Z_smul_mulVec__f726d66f1ccf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:48.002201+00:00
-- url     : https://prove2.me/theorems/8eb3ad08-a3e7-4766-bc80-ec234610debd
-- title:
--   P2 M Positivity Theory Rg Sw WR Z smul mul Vec  f726d66f1ccf: P2 M Positivity Theory Rg Sw WR Z smul mul Vec  f726d66f1ccf
-- statement:
--   The P2 M Positivity Theory Rg Sw WR Z smul mul Vec  f726d66f1ccf construction uses the P2 M Positivity Theory Rg Sw WR Z smul mul Vec  f726d66f1ccf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L35-L37

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

theorem P2M_PositivityTheory_Rg_Sw_WR_Z_smul_mulVec__f726d66f1ccf (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : (c • M) *ᵥ v = c • (M *ᵥ v) := by sorry

alias «PositivityTheory».«Rg».«Sw».«WR».«Z».«smul_mulVec'» := P2M_PositivityTheory_Rg_Sw_WR_Z_smul_mulVec__f726d66f1ccf
