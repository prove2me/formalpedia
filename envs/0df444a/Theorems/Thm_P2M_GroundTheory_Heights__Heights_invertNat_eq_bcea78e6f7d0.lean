-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_invertNat_eq_bcea78e6f7d0
-- name    : P2M_GroundTheory_Heights__Heights_invertNat_eq_bcea78e6f7d0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:03.56265+00:00
-- url     : https://prove2.me/theorems/7f87aa64-f5c8-51a6-8e8e-673b29fa7a69
-- title:
--   P2 M Ground Theory Heights  Heights invert Nat eq bcea78e6f7d0: P2 M Ground Theory Heights  Heights invert Nat eq bcea78e6f7d0
-- statement:
--   The P2 M Ground Theory Heights  Heights invert Nat eq bcea78e6f7d0 construction uses the P2 M Ground Theory Heights  Heights invert Nat eq bcea78e6f7d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L35-L38

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
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_invertNat_eq_bcea78e6f7d0 (m : ℕ) (A : Subalgebra ℤ Ω) :
    invertNat m A.toSubring = (IndefiniteRowSideFullHecke.Antisym.invertNat A m).toSubring := by sorry

alias «GroundTheory».«Heights₂».«Heights».«invertNat_eq» := P2M_GroundTheory_Heights__Heights_invertNat_eq_bcea78e6f7d0
