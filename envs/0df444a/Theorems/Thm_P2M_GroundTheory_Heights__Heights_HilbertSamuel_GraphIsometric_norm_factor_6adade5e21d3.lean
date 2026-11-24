-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_norm_factor_6adade5e21d3
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_norm_factor_6adade5e21d3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:03.391529+00:00
-- url     : https://prove2.me/theorems/9359e971-6d22-4434-b693-4ee1445d0645
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric norm factor 6adade5e21d3: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric norm factor 6adade5e21d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric norm factor 6adade5e21d3 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric norm factor 6adade5e21d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L190-L194

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_norm_factor_6adade5e21d3 {l : ℝ} (hl : l ≠ 0) (t : ℝ) (e : ℤ) :
    t ^ e.toNat * (l * t) ^ (-e).toNat * l ^ e = (l * t) ^ e.toNat * t ^ (-e).toNat := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«norm_factor» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_norm_factor_6adade5e21d3
