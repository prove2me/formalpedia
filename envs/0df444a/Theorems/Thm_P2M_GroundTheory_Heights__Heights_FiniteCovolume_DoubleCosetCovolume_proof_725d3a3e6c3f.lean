-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_proof_725d3a3e6c3f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_proof_725d3a3e6c3f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:48.073237+00:00
-- url     : https://prove2.me/theorems/05f502ef-0fdf-4aef-8ed3-013c345440cf
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume proof 725d3a3e6c3f: P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume proof 725d3a3e6c3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume proof 725d3a3e6c3f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Double Coset Covolume proof 725d3a3e6c3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L130-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L130-L263

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_proof_725d3a3e6c3f (G G₁ G₂ : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] :
    DoubleCosetCovolume.Statement G G₁ G₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«DoubleCosetCovolume».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_proof_725d3a3e6c3f
