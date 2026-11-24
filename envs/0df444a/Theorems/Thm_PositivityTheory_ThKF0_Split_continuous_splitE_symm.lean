-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Split_continuous_splitE_symm
-- name    : PositivityTheory.ThKF0.Split.continuous_splitE_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:28.554115+00:00
-- url     : https://prove2.me/theorems/9aadf333-b80d-4040-bcc1-d11a27456557
-- title:
--   Split: continuous split E symm
-- statement:
--   The Split construction uses the continuous split E symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSplit.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSplit.lean#L46-L51

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory
open scoped ENNReal Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Split
variable (F : Type) [Field F] [NumberField F] (κ : Type)

theorem PositivityTheory.ThKF0.Split.continuous_splitE_symm : Continuous (splitE F κ).symm := by sorry
