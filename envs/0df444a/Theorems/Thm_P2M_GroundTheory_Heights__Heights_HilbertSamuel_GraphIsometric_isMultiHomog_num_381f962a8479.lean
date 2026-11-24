-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_num_381f962a8479
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_num_381f962a8479
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:13.69651+00:00
-- url     : https://prove2.me/theorems/66b3969b-7108-4c71-ba96-865b21caa927
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog num 381f962a8479: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog num 381f962a8479
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog num 381f962a8479 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric is Multi Homog num 381f962a8479 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L109-L114

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_num_381f962a8479 [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) :
    IsMultiHomog (num A j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inl k) 1 + (-a k).toNat • Pi.single (Sum.inr k) 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«isMultiHomog_num» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_num_381f962a8479
