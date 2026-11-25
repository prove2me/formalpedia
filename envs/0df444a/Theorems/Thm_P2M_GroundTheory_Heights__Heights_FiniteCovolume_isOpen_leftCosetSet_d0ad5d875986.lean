-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isOpen_leftCosetSet_d0ad5d875986
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_isOpen_leftCosetSet_d0ad5d875986
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:02.248177+00:00
-- url     : https://prove2.me/theorems/77c2f07d-6fc6-4b8b-8f67-aea5cb9e1ca9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume is Open left Coset Set d0ad5d875986: P2 M Ground Theory Heights  Heights Finite Covolume is Open left Coset Set d0ad5d875986
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume is Open left Coset Set d0ad5d875986 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume is Open left Coset Set d0ad5d875986 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L34-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_isOpen_leftCosetSet_d0ad5d875986 {K : Subgroup G₂} (hK : IsOpen (K : Set G₂)) (s : G₂) :
    IsOpen (leftCosetSet K s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«isOpen_leftCosetSet» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_isOpen_leftCosetSet_d0ad5d875986
