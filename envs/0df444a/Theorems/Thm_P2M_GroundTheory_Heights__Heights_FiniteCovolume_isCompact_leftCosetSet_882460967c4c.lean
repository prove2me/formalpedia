-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isCompact_leftCosetSet_882460967c4c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_isCompact_leftCosetSet_882460967c4c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:52.782873+00:00
-- url     : https://prove2.me/theorems/9092fa42-d168-4ebe-97f0-3c7569491553
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume is Compact left Coset Set 882460967c4c: P2 M Ground Theory Heights  Heights Finite Covolume is Compact left Coset Set 882460967c4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume is Compact left Coset Set 882460967c4c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume is Compact left Coset Set 882460967c4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L38-L43

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_isCompact_leftCosetSet_882460967c4c {K : Subgroup G₂} (hK : IsCompact (K : Set G₂)) (s : G₂) :
    IsCompact (leftCosetSet K s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«isCompact_leftCosetSet» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_isCompact_leftCosetSet_882460967c4c
