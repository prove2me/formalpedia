-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pullbackLat_eq_pullLat_336b93e51c3f
-- name    : P2M_GroundTheory_Heights__Heights_pullbackLat_eq_pullLat_336b93e51c3f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:22.044926+00:00
-- url     : https://prove2.me/theorems/9e8f56df-f1ff-57aa-a013-055bf4da885c
-- title:
--   P2 M Ground Theory Heights  Heights pullback Lat eq pull Lat 336b93e51c3f: P2 M Ground Theory Heights  Heights pullback Lat eq pull Lat 336b93e51c3f
-- statement:
--   The P2 M Ground Theory Heights  Heights pullback Lat eq pull Lat 336b93e51c3f construction uses the P2 M Ground Theory Heights  Heights pullback Lat eq pull Lat 336b93e51c3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L120-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}

theorem P2M_GroundTheory_Heights__Heights_pullbackLat_eq_pullLat_336b93e51c3f {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {x : ι → Ω}
    (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ) :
    pullbackLat B z q = IndefiniteRowSideFullHecke.Antisym.pullLat x z B.lat q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pullbackLat_eq_pullLat» := P2M_GroundTheory_Heights__Heights_pullbackLat_eq_pullLat_336b93e51c3f
