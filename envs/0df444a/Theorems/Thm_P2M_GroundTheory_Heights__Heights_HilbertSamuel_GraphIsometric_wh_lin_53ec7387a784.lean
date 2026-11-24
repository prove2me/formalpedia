-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_wh_lin_53ec7387a784
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_wh_lin_53ec7387a784
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:35.101384+00:00
-- url     : https://prove2.me/theorems/d881224a-7db7-42c8-8a24-67fbe2690879
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric wh lin 53ec7387a784: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric wh lin 53ec7387a784
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric wh lin 53ec7387a784 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric wh lin 53ec7387a784 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L100-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L100-L107

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_wh_lin_53ec7387a784 [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (q : Σ k, ι₂ k) :
    IsWeightedHomogeneous (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (Sum.elim ι ι₂))
      (rename inlV (linForm A q)) (Pi.single (Sum.inl q.1) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«wh_lin» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_wh_lin_53ec7387a784
