-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_rename_mem_graphIdeal_dea023b31391
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_rename_mem_graphIdeal_dea023b31391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:27.086495+00:00
-- url     : https://prove2.me/theorems/e3b62b99-bcc1-4ff9-9834-5b5952d7bdaf
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms rename mem graph Ideal dea023b31391: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms rename mem graph
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms rename mem graph Ideal dea023b31391 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms rename mem graph Ideal dea023b31391 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L64-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_rename_mem_graphIdeal_dea023b31391 {P : Ideal (MRing ι)} (g : (Σ k, ι₂ k) → MRing ι) {p : MRing ι} (hp : p ∈ P) :
    rename inlV p ∈ graphIdeal P g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«rename_mem_graphIdeal» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_rename_mem_graphIdeal_dea023b31391
