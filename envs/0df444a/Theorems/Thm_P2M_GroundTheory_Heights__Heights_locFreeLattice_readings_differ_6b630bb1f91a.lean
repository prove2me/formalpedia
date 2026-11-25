-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_locFreeLattice_readings_differ_6b630bb1f91a
-- name    : P2M_GroundTheory_Heights__Heights_locFreeLattice_readings_differ_6b630bb1f91a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:35.441268+00:00
-- url     : https://prove2.me/theorems/7b316d1e-d44f-5784-9083-aff0e96da9f2
-- title:
--   P2 M Ground Theory Heights  Heights loc Free Lattice readings differ 6b630bb1f91a: P2 M Ground Theory Heights  Heights loc Free Lattice readings differ 6b630bb1f91a
-- statement:
--   The P2 M Ground Theory Heights  Heights loc Free Lattice readings differ 6b630bb1f91a construction uses the P2 M Ground Theory Heights  Heights loc Free Lattice readings differ 6b630bb1f91a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L272-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L272-L276

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

theorem P2M_GroundTheory_Heights__Heights_locFreeLattice_readings_differ_6b630bb1f91a :
    ∃ L : Submodule zTwo ℝ,
      (Module.Finite zTwo L ∧ Module.Projective zTwo L ∧ Submodule.span ℝ (L : Set ℝ) = ⊤) ∧
      ∀ r, ¬ IsLocFreeLattice (locPrimeTo chartOne 2) r L.toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«locFreeLattice_readings_differ» := P2M_GroundTheory_Heights__Heights_locFreeLattice_readings_differ_6b630bb1f91a
