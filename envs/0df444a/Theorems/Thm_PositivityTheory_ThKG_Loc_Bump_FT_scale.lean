-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_scale
-- name    : PositivityTheory.ThKG.Loc.Bump.FT_scale
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:27.833609+00:00
-- url     : https://prove2.me/theorems/96b68af2-601d-51d0-867b-5f1fab15829b
-- title:
--   Bump: FT scale
-- statement:
--   The Bump construction uses the FT scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L94-L105

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

theorem PositivityTheory.ThKG.Loc.Bump.FT_scale {m : (ι → ℂ) → ℂ} (hm : Integrable m) {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) (x : ι → ℂ) :
    FT (fun t => m (y * t)) x = ((nm y : ℝ) : ℂ)⁻¹ * FT m (x * y⁻¹) := by sorry
