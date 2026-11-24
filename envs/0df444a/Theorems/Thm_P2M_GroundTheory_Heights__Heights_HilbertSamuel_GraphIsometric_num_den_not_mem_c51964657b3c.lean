-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_num_den_not_mem_c51964657b3c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_num_den_not_mem_c51964657b3c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:47.678899+00:00
-- url     : https://prove2.me/theorems/fffd1bff-8781-4228-80ad-567d058963c7
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric num den not mem c51964657b3c: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric num den not mem c51964657b3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric num den not mem c51964657b3c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric num den not mem c51964657b3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L123-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L123-L139

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_num_den_not_mem_c51964657b3c {P : Ideal (MRing ι)} (hP : P.IsPrime) (A : ∀ k, ι₂ k → ι k → ℤ) {j : ∀ k, ι₂ k}
    (hj : ∀ k, linForm A ⟨k, j k⟩ ∉ P) (a : K → ℤ) :
    num A j a ∉ graphIdeal P (linForm A) ∧ den A j a ∉ graphIdeal P (linForm A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«num_den_not_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_num_den_not_mem_c51964657b3c
