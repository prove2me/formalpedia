-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_Pm_Pm
-- name    : PositivityTheory.ThKH.Locrep.Pm_Pm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:00:52.464907+00:00
-- url     : https://prove2.me/theorems/d2e1c100-2ca6-5158-a902-fe7a978fa0d1
-- title:
--   Locrep: Pm Pm
-- statement:
--   The Locrep construction uses the Pm Pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L32-L36

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
variable {ev ι}

theorem PositivityTheory.ThKH.Locrep.Pm_Pm (h : ∀ y, ev (ι y) = y) (φ φ₁ : K → ℂ) (a y : K) (Φ : A → ℂ) :
    Pm ev ι φ a (Pm ev ι φ₁ y Φ) = φ₁ a • Pm ev ι φ y Φ := by sorry
