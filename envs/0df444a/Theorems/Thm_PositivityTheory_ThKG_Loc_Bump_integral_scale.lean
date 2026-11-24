-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integral_scale
-- name    : PositivityTheory.ThKG.Loc.Bump.integral_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:20.862673+00:00
-- url     : https://prove2.me/theorems/fb4a6f1d-64c3-4d71-a2b7-09ca6dc97248
-- title:
--   Bump: integral scale
-- statement:
--   The Bump construction uses the integral scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L39-L42

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

theorem PositivityTheory.ThKG.Loc.Bump.integral_scale {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → E}
    (hg : AEStronglyMeasurable g volume) : ∫ x, g (y * x) = (nm y)⁻¹ • ∫ x, g x := by sorry
