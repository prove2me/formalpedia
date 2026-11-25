-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_lt_top_261478f0703a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_lt_top_261478f0703a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:54.144858+00:00
-- url     : https://prove2.me/theorems/e58ee35e-bb8a-411a-bcc1-8bbd8fbade9e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod lt top 261478f0703a: P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod lt top 261478f0703a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod lt top 261478f0703a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod lt top 261478f0703a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L121-L126

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
variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_lt_top_261478f0703a (hV : IsOpen V) (hVc : IsCompact V) {A : Set G₁}
    (hA : (Measure.haar : Measure G₁) A < ∞) : μ (Φ ⁻¹' (A ×ˢ V)) < ∞ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measure_preimage_prod_lt_top» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_lt_top_261478f0703a
