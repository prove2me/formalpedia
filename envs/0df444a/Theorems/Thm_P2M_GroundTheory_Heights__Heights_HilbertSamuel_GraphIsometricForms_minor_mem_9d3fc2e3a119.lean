-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_minor_mem_9d3fc2e3a119
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_minor_mem_9d3fc2e3a119
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:46.111888+00:00
-- url     : https://prove2.me/theorems/18378b62-ef91-41d7-a8cd-d07b50c78cc0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms minor mem 9d3fc2e3a119: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms minor mem 9d3fc2e3a119
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms minor mem 9d3fc2e3a119 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms minor mem 9d3fc2e3a119 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L68-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_minor_mem_663e0dfb408f

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_minor_mem_9d3fc2e3a119 (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (k : K₂) (j₁ j₂ : ι₂ k) :
    X (inrV ⟨k, j₁⟩) * rename inlV (g ⟨k, j₂⟩) - X (inrV ⟨k, j₂⟩) * rename inlV (g ⟨k, j₁⟩) ∈
      graphIdeal P g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«minor_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_minor_mem_9d3fc2e3a119
