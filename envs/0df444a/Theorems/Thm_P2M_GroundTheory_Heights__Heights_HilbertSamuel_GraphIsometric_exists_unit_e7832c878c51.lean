-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_exists_unit_e7832c878c51
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_exists_unit_e7832c878c51
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:54.098626+00:00
-- url     : https://prove2.me/theorems/b6e32ffd-b6b6-4731-b3b8-e4817080c6f3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric exists unit e7832c878c51: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric exists unit e7832c878c51
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric exists unit e7832c878c51 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric exists unit e7832c878c51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L141-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L141-L188

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_exists_unit_e7832c878c51 {P : Ideal (MRing ι)} {A : ∀ k, ι₂ k → ι k → ℤ} (hBP : IsBasePtFree P (linForm A))
    (j : ∀ k, ι₂ k) (a : K → ℤ) {W : Ideal (MRing (Sum.elim ι ι₂))} (hW : W.IsPrime)
    (hΓW : graphIdeal P (linForm A) ≤ W) (hrel : IsRelevant W) :
    ∃ u v, u ∉ W ∧ v ∉ W ∧ u * num A j a - v * den A j a ∈ graphIdeal P (linForm A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«exists_unit» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_exists_unit_e7832c878c51
