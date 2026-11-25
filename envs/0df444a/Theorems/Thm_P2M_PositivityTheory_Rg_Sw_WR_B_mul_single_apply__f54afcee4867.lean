-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_B_mul_single_apply__f54afcee4867
-- name    : P2M_PositivityTheory_Rg_Sw_WR_B_mul_single_apply__f54afcee4867
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:10:35.238113+00:00
-- url     : https://prove2.me/theorems/8993fbf7-0e65-48cf-9d22-77b806c062f9
-- title:
--   P2 M Positivity Theory Rg Sw WR B mul single apply  f54afcee4867: P2 M Positivity Theory Rg Sw WR B mul single apply  f54afcee4867
-- statement:
--   The P2 M Positivity Theory Rg Sw WR B mul single apply  f54afcee4867 construction uses the P2 M Positivity Theory Rg Sw WR B mul single apply  f54afcee4867 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L121-L127

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_WR_B_mul_single_apply__f54afcee4867 (M : Matrix (Fin n) (Fin n) ℂ) (a c k l : Fin n) :
    (M * Matrix.single l k (1 : ℂ)) a c = if k = c then M a l else 0 := by sorry

alias «PositivityTheory».«Rg».«Sw».«WR».«B».«mul_single_apply'» := P2M_PositivityTheory_Rg_Sw_WR_B_mul_single_apply__f54afcee4867
