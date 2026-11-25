-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_rename_inlV_d9fcf2f5633e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_rename_inlV_d9fcf2f5633e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:04.48181+00:00
-- url     : https://prove2.me/theorems/1acac147-cc5f-4021-8894-657fce69ba9f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map rename inl V d9fcf2f5633e: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map rename
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map rename inl V d9fcf2f5633e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms graph Map rename inl V d9fcf2f5633e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L53-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_rename_inlV_833d0140fb95

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_rename_inlV_d9fcf2f5633e (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : MRing ι) :
    graphMap P g (rename inlV p) = C (Ideal.Quotient.mk P p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«graphMap_rename_inlV» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_rename_inlV_d9fcf2f5633e
