-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_limsupExt_max_le_2c44b518e346
-- name    : P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_limsupExt_max_le_2c44b518e346
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.843674+00:00
-- url     : https://prove2.me/theorems/9f41078f-f736-4fd3-9754-ce60966a33a3
-- title:
--   P2 M Ground Theory Heights  Heights Regular Trunc Transfer limsup Ext max le 2c44b518e346: P2 M Ground Theory Heights  Heights Regular Trunc Transfer limsup Ext max le 2c44b518e346
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Trunc Transfer limsup Ext max le 2c44b518e346 construction uses the P2 M Ground Theory Heights  Heights Regular Trunc Transfer limsup Ext max le 2c44b518e346 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L33-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.TruncTransfer

theorem P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_limsupExt_max_le_2c44b518e346 {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) (S : Finset (Fin D))
    (v : (Fin D → ℂ) → ℝ) (K c r : ℝ) {y : Fin D → ℂ} (hy : y ∈ U) (hr : 0 < r)
    (h : ∀ y' ∈ ball y r, y' ∈ U → y' ∉ coordDiv S → max (v y') (-K) ≤ c) :
    limsupExt U (coordDiv S) (fun y' => max (v y') (-K)) y ≤ c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«TruncTransfer».«limsupExt_max_le» := P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_limsupExt_max_le_2c44b518e346
