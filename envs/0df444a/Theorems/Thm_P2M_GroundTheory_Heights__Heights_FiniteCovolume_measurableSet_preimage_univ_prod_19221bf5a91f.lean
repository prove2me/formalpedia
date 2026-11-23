-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_preimage_univ_prod_19221bf5a91f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_preimage_univ_prod_19221bf5a91f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:15.350974+00:00
-- url     : https://prove2.me/theorems/2cbfd6bd-d604-4165-8821-580b49253b66
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measurable Set preimage univ prod 19221bf5a91f: P2 M Ground Theory Heights  Heights Finite Covolume measurable Set preimage univ prod 19221bf5a91f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measurable Set preimage univ prod 19221bf5a91f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measurable Set preimage univ prod 19221bf5a91f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L53-L54

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
variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_preimage_univ_prod_19221bf5a91f (hV : IsOpen V) : MeasurableSet (Φ ⁻¹' (univ ×ˢ V)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measurableSet_preimage_univ_prod» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_preimage_univ_prod_19221bf5a91f
