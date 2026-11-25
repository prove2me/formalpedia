-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mem_divSupp_and_multAt_eq_afb478e7eb95
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mem_divSupp_and_multAt_eq_afb478e7eb95
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:12.716433+00:00
-- url     : https://prove2.me/theorems/7dc0af18-1439-4f1f-b541-f95dbf3e1e39
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mem div Supp and mult At eq afb478e7eb95: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mem div Supp and mult At
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mem div Supp and mult At eq afb478e7eb95 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mem div Supp and mult At eq afb478e7eb95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L31-L43

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mem_divSupp_and_multAt_eq_afb478e7eb95 {P W : Ideal (MRing κ)} {f g u v : MRing κ} (hf : W ∈ divSupp P f)
    (hu : u ∉ W) (hv : v ∉ W) (huv : u * f - v * g ∈ P) :
    W ∈ divSupp P g ∧ multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«mem_divSupp_and_multAt_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mem_divSupp_and_multAt_eq_afb478e7eb95
