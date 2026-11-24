-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_int_of_le
-- name    : PositivityTheory.ThKG.Loc.Bump.int_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:06.141553+00:00
-- url     : https://prove2.me/theorems/9a031e52-e0ad-458a-86d7-eaf07a7355da
-- title:
--   Bump: int of le
-- statement:
--   The Bump construction uses the int of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L135-L141

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKG.Loc.Bump.int_of_le {g : ℂ → ℂ} (hg : Measurable g) (C : ℝ) (h : ∀ z, z ≠ 0 → ‖g z‖ * (1 + ‖z‖) ^ 3 ≤ C) : Integrable g := by sorry
