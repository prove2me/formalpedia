-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_isSp_fE
-- name    : PositivityTheory.ThKF0.Chr.isSp_fE
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:32.659249+00:00
-- url     : https://prove2.me/theorems/12b194aa-1b8c-467e-b0d0-abfb58979498
-- title:
--   Chr: is Sp f E
-- statement:
--   The Chr construction uses the is Sp f E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L73-L75

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]

theorem PositivityTheory.ThKF0.Chr.isSp_fE : IsSp (fE R κ) := by sorry
