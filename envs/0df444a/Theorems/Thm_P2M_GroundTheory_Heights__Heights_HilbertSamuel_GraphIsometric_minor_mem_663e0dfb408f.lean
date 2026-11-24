-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_minor_mem_663e0dfb408f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_minor_mem_663e0dfb408f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:53.00082+00:00
-- url     : https://prove2.me/theorems/a31a4128-811c-4291-a5ed-84cdc91a760a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric minor mem 663e0dfb408f: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric minor mem 663e0dfb408f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric minor mem 663e0dfb408f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric minor mem 663e0dfb408f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L87-L92

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_minor_mem_663e0dfb408f (P : Ideal (MRing ι)) (A : ∀ k, ι₂ k → ι k → ℤ) (k : K) (j₁ j₂ : ι₂ k) :
    X (inrV ⟨k, j₁⟩) * rename inlV (linForm A ⟨k, j₂⟩) - X (inrV ⟨k, j₂⟩) * rename inlV (linForm A ⟨k, j₁⟩) ∈
      graphIdeal P (linForm A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«minor_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_minor_mem_663e0dfb408f
