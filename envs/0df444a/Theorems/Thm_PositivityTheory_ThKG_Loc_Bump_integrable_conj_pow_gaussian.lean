-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_conj_pow_gaussian
-- name    : PositivityTheory.ThKG.Loc.Bump.integrable_conj_pow_gaussian
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:36.895688+00:00
-- url     : https://prove2.me/theorems/88e68b22-dc3e-4f14-a9c4-fc731647e3ad
-- title:
--   Bump: integrable conj pow gaussian
-- statement:
--   The Bump construction uses the integrable conj pow gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L150-L151

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

theorem PositivityTheory.ThKG.Loc.Bump.integrable_conj_pow_gaussian (k : ℕ) : Integrable fun z : ℂ => conj z ^ k * Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2) := by sorry
