-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_measurable_dens
-- name    : PositivityTheory.ThKG.Loc.Bump.measurable_dens
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:02.263665+00:00
-- url     : https://prove2.me/theorems/c707041d-60d0-4762-9f53-0a963f60e24b
-- title:
--   Bump: measurable dens
-- statement:
--   The Bump construction uses the measurable dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/DictHaar.lean#L28-L30

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar
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
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKG.Loc.Bump.measurable_dens : Measurable (dens : (ι → ℂ) → ℝ≥0) := by sorry
