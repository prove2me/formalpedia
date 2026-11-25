-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_locAtIntPrime_eq_locPrimeTo_4bb9be37f9c6
-- name    : P2M_GroundTheory_Heights__Heights_locAtIntPrime_eq_locPrimeTo_4bb9be37f9c6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:30.188512+00:00
-- url     : https://prove2.me/theorems/d45c3665-5e80-43c3-a46c-358fc9765d69
-- title:
--   P2 M Ground Theory Heights  Heights loc At Int Prime eq loc Prime To 4bb9be37f9c6: P2 M Ground Theory Heights  Heights loc At Int Prime eq loc Prime To 4bb9be37f9c6
-- statement:
--   The P2 M Ground Theory Heights  Heights loc At Int Prime eq loc Prime To 4bb9be37f9c6 construction uses the P2 M Ground Theory Heights  Heights loc At Int Prime eq loc Prime To 4bb9be37f9c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L16-L33

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

theorem P2M_GroundTheory_Heights__Heights_locAtIntPrime_eq_locPrimeTo_4bb9be37f9c6 (p : ℕ) (A : Subalgebra ℤ Ω) :
    locAtIntPrime p A.toSubring = (IndefiniteRowSideFullHecke.Antisym.locPrimeTo A p).toSubring := by sorry

alias «GroundTheory».«Heights₂».«Heights».«locAtIntPrime_eq_locPrimeTo» := P2M_GroundTheory_Heights__Heights_locAtIntPrime_eq_locPrimeTo_4bb9be37f9c6
