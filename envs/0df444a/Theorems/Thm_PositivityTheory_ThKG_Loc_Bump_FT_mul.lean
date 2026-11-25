-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_mul
-- name    : PositivityTheory.ThKG.Loc.Bump.FT_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:20.684799+00:00
-- url     : https://prove2.me/theorems/2cb135be-cf85-58b1-a13e-7a6ad2926232
-- title:
--   Bump: FT mul
-- statement:
--   The Bump construction uses the FT mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L84-L92

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

theorem PositivityTheory.ThKG.Loc.Bump.FT_mul {h m : (ι → ℂ) → ℂ} (hh : Integrable h) (hm : Integrable m) : ∫ t, FT h t * m t = ∫ x, h x * FT m x := by sorry
