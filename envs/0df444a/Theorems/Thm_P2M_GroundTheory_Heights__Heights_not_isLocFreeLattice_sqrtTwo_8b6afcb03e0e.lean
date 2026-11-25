-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_isLocFreeLattice_sqrtTwo_8b6afcb03e0e
-- name    : P2M_GroundTheory_Heights__Heights_not_isLocFreeLattice_sqrtTwo_8b6afcb03e0e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:29.895027+00:00
-- url     : https://prove2.me/theorems/5a5a9eb5-effd-4b2f-b16e-171a1b9651b3
-- title:
--   P2 M Ground Theory Heights  Heights not is Loc Free Lattice sqrt Two 8b6afcb03e0e: P2 M Ground Theory Heights  Heights not is Loc Free Lattice sqrt Two 8b6afcb03e0e
-- statement:
--   The P2 M Ground Theory Heights  Heights not is Loc Free Lattice sqrt Two 8b6afcb03e0e construction uses the P2 M Ground Theory Heights  Heights not is Loc Free Lattice sqrt Two 8b6afcb03e0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L244-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L244-L270

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
open IndefiniteRowSideFullHecke.Antisym

theorem P2M_GroundTheory_Heights__Heights_not_isLocFreeLattice_sqrtTwo_8b6afcb03e0e (r : ℕ) :
    ¬ IsLocFreeLattice (locPrimeTo chartOne 2) r sqrtTwoLattice.toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«not_isLocFreeLattice_sqrtTwo» := P2M_GroundTheory_Heights__Heights_not_isLocFreeLattice_sqrtTwo_8b6afcb03e0e
