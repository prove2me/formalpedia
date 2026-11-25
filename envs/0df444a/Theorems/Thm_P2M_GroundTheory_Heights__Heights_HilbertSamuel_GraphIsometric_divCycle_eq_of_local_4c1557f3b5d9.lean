-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_divCycle_eq_of_local_4c1557f3b5d9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_divCycle_eq_of_local_4c1557f3b5d9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:08.984739+00:00
-- url     : https://prove2.me/theorems/ad462a67-c509-4315-8b17-acf8deb3d4d9
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric div Cycle eq of local 4c1557f3b5d9: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric div Cycle eq of local 4c1557f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric div Cycle eq of local 4c1557f3b5d9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric div Cycle eq of local 4c1557f3b5d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L45-L58

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
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_divCycle_eq_of_local_4c1557f3b5d9 {P : Ideal (MRing κ)} {f g : MRing κ}
    (h : ∀ W : Ideal (MRing κ), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    divCycle P f = divCycle P g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«divCycle_eq_of_local» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_divCycle_eq_of_local_4c1557f3b5d9
