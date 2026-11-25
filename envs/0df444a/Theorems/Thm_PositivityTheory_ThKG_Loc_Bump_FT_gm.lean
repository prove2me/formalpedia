-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_gm
-- name    : PositivityTheory.ThKG.Loc.Bump.FT_gm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:19.689184+00:00
-- url     : https://prove2.me/theorems/bc7995af-a08a-58b5-ba92-5fa1926f0fe6
-- title:
--   Bump: FT gm
-- statement:
--   The Bump construction uses the FT gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L160-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L160-L174

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

theorem PositivityTheory.ThKG.Loc.Bump.FT_gm (κ : ι → ℕ) (x : ι → ℂ) :
    FT (gm κ) x = ∏ w, (2⁻¹ * (-Complex.I) ^ κ w) * (x w ^ κ w * Complex.exp (-2 * Real.pi * (‖x w‖ : ℂ) ^ 2)) := by sorry
