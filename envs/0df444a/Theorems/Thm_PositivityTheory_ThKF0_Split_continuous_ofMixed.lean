-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Split_continuous_ofMixed
-- name    : PositivityTheory.ThKF0.Split.continuous_ofMixed
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:59.796542+00:00
-- url     : https://prove2.me/theorems/4097bb77-eab7-4c79-8ade-5cd8696add6e
-- title:
--   Split: continuous of Mixed
-- statement:
--   The Split construction uses the continuous of Mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSplit.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSplit.lean#L20-L28

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

theorem PositivityTheory.ThKF0.Split.continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by sorry
