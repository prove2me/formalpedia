-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_den_b8412c92fdca
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_den_b8412c92fdca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:04.363563+00:00
-- url     : https://prove2.me/theorems/7e290605-dc5b-4efb-b2a4-cbf938a55c49
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog den b8412c92fdca: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog den b8412c92fdca
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog den b8412c92fdca construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog den b8412c92fdca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L116-L121

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_den_b8412c92fdca [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) :
    IsMultiHomog (den A j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inr k) 1 + (-a k).toNat • Pi.single (Sum.inl k) 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«isMultiHomog_den» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_den_b8412c92fdca
