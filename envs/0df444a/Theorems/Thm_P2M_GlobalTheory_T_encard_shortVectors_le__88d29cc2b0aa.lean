-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_encard_shortVectors_le__88d29cc2b0aa
-- name    : P2M_GlobalTheory_T_encard_shortVectors_le__88d29cc2b0aa
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:55:51.115891+00:00
-- url     : https://prove2.me/theorems/cbc84427-edc4-40a4-95cc-92a21b6d698a
-- title:
--   P2 M Global Theory T encard short Vectors le  88d29cc2b0aa: P2 M Global Theory T encard short Vectors le  88d29cc2b0aa
-- statement:
--   The P2 M Global Theory T encard short Vectors le  88d29cc2b0aa construction uses the P2 M Global Theory T encard short Vectors le  88d29cc2b0aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardShortVectorsLeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardShortVectorsLeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_encard_shortVectors_le__88d29cc2b0aa : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ B : ℝ, 0 ≤ B → (({x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt B) ^ (2 * Module.finrank K V * fDeg K)) := by sorry

alias «GlobalTheory».«T».«encard_shortVectors_le'» := P2M_GlobalTheory_T_encard_shortVectors_le__88d29cc2b0aa
