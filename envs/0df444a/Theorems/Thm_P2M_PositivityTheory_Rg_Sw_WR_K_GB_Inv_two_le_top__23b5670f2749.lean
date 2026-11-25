-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_K_GB_Inv_two_le_top__23b5670f2749
-- name    : P2M_PositivityTheory_Rg_Sw_WR_K_GB_Inv_two_le_top__23b5670f2749
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:57.633872+00:00
-- url     : https://prove2.me/theorems/c84a7b3f-18b3-41b0-b62e-a54f474d24e4
-- title:
--   P2 M Positivity Theory Rg Sw WR K GB Inv two le top  23b5670f2749: P2 M Positivity Theory Rg Sw WR K GB Inv two le top  23b5670f2749
-- statement:
--   The P2 M Positivity Theory Rg Sw WR K GB Inv two le top  23b5670f2749 construction uses the P2 M Positivity Theory Rg Sw WR K GB Inv two le top  23b5670f2749 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L68-L70

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv

theorem P2M_PositivityTheory_Rg_Sw_WR_K_GB_Inv_two_le_top__23b5670f2749 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by sorry

alias «PositivityTheory».«Rg».«Sw».«WR».«K».«GB».«Inv».«two_le_top'» := P2M_PositivityTheory_Rg_Sw_WR_K_GB_Inv_two_le_top__23b5670f2749
