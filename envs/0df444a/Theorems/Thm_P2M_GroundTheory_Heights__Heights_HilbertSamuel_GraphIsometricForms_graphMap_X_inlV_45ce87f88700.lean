-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_X_inlV_45ce87f88700
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_X_inlV_45ce87f88700
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:30.746026+00:00
-- url     : https://prove2.me/theorems/2e469b4c-0479-4b86-8355-c2b40f3b0b59
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map X inl V 45ce87f88700: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map X inl V 45ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map X inl V 45ce87f88700 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map X inl V 45ce87f88700 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L43-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inlV_57139c30c413

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_X_inlV_45ce87f88700 (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : Σ k, ι k) :
    graphMap P g (X (inlV p)) = C (Ideal.Quotient.mk P (X p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«graphMap_X_inlV» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_X_inlV_45ce87f88700
