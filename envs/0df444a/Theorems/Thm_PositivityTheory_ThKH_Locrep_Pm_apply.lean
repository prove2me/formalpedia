-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_Pm_apply
-- name    : PositivityTheory.ThKH.Locrep.Pm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:07.967269+00:00
-- url     : https://prove2.me/theorems/9b07f1d8-74ca-4548-bce0-750f4cd857a5
-- title:
--   Locrep: Pm apply
-- statement:
--   The Locrep construction uses the Pm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L18-L18

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

theorem PositivityTheory.ThKH.Locrep.Pm_apply (φ : K → ℂ) (y : K) (Φ : A → ℂ) (x : A) : Pm ev ι φ y Φ x = φ (ev x) * Φ (put ev ι x y) := by sorry
