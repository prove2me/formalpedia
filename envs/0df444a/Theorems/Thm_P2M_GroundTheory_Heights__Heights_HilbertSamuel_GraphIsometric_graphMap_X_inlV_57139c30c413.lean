-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inlV_57139c30c413
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inlV_57139c30c413
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:26.032569+00:00
-- url     : https://prove2.me/theorems/ca33218d-0b39-47db-9a7c-daba8bb340ad
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric graph Map X inl V 57139c30c413: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric graph Map X inl V 57139c30c413
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric graph Map X inl V 57139c30c413 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric graph Map X inl V 57139c30c413 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
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
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inlV_57139c30c413 (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : Σ k, ι k) :
    graphMap P g (X (inlV p)) = C (Ideal.Quotient.mk P (X p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«graphMap_X_inlV» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inlV_57139c30c413
