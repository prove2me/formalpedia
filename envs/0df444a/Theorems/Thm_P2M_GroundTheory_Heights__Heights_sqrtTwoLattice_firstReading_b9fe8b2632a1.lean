-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sqrtTwoLattice_firstReading_b9fe8b2632a1
-- name    : P2M_GroundTheory_Heights__Heights_sqrtTwoLattice_firstReading_b9fe8b2632a1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:40.889727+00:00
-- url     : https://prove2.me/theorems/f22fa436-1c45-445e-aa43-dd949c0fcbd1
-- title:
--   P2 M Ground Theory Heights  Heights sqrt Two Lattice first Reading b9fe8b2632a1: P2 M Ground Theory Heights  Heights sqrt Two Lattice first Reading b9fe8b2632a1
-- statement:
--   The P2 M Ground Theory Heights  Heights sqrt Two Lattice first Reading b9fe8b2632a1 construction uses the P2 M Ground Theory Heights  Heights sqrt Two Lattice first Reading b9fe8b2632a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L232-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L232-L242

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

theorem P2M_GroundTheory_Heights__Heights_sqrtTwoLattice_firstReading_b9fe8b2632a1 :
    Module.Finite zTwo sqrtTwoLattice ∧ Module.Projective zTwo sqrtTwoLattice ∧
      Submodule.span ℝ (sqrtTwoLattice : Set ℝ) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sqrtTwoLattice_firstReading» := P2M_GroundTheory_Heights__Heights_sqrtTwoLattice_firstReading_b9fe8b2632a1
