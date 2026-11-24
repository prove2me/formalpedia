-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_gauss
-- name    : PositivityTheory.ThKG.Loc.Bump.norm_gauss
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:00.938947+00:00
-- url     : https://prove2.me/theorems/599c712b-8d3d-4a68-a689-b5b26eb84eb2
-- title:
--   Bump: norm gauss
-- statement:
--   The Bump construction uses the norm gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L123-L125

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

theorem PositivityTheory.ThKG.Loc.Bump.norm_gauss (z : ℂ) : ‖Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2)‖ = Real.exp (-2 * Real.pi * ‖z‖ ^ 2) := by sorry
