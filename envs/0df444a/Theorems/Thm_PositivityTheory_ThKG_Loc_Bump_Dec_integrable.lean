-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_Dec_integrable
-- name    : PositivityTheory.ThKG.Loc.Bump.Dec.integrable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:22.971863+00:00
-- url     : https://prove2.me/theorems/e0df6ccb-8981-553c-9fc5-6d791260343e
-- title:
--   Dec: integrable
-- statement:
--   The Dec construction uses the integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean#L112-L114

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
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
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
omit [TopologicalSpace K]

theorem PositivityTheory.ThKG.Loc.Bump.Dec.integrable {a : K × (ι → ℂ) → ℂ} (hd : Dec a) (k : K) (ha : Continuous fun x => a (k, x)) : Integrable fun x => a (k, x) := by sorry
