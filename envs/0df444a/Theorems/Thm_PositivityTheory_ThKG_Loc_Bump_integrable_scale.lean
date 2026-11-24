-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_scale
-- name    : PositivityTheory.ThKG.Loc.Bump.integrable_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:21.154788+00:00
-- url     : https://prove2.me/theorems/2167f252-cc12-4d38-bd98-5b810db0e021
-- title:
--   Bump: integrable scale
-- statement:
--   The Bump construction uses the integrable scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L44-L47

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

theorem PositivityTheory.ThKG.Loc.Bump.integrable_scale {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → ℂ} (hg : Integrable g) : Integrable fun x => g (y * x) := by sorry
