-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_rationalWeight_ne_zero
-- name    : PositivityTheory.ThKG.Loc.Bump.rationalWeight_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:16.471094+00:00
-- url     : https://prove2.me/theorems/730553e0-4728-47a0-ac19-53de1fcde1c4
-- title:
--   Bump: rational Weight ne zero
-- statement:
--   The Bump construction uses the rational Weight ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L114-L115

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

theorem PositivityTheory.ThKG.Loc.Bump.rationalWeight_ne_zero (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) : r0 κ e x ≠ 0 := by sorry
