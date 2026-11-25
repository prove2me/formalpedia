-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mul_mem_sup_span_b3608818911e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mul_mem_sup_span_b3608818911e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:56.960724+00:00
-- url     : https://prove2.me/theorems/454bc2d0-f403-4b16-9dd2-c0d186bf355b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mul mem sup span b3608818911e: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mul mem sup span b3608818911e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mul mem sup span b3608818911e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric mul mem sup span b3608818911e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean#L21-L29

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mul_mem_sup_span_b3608818911e {P : Ideal (MRing κ)} {f g u v : MRing κ} (huv : u * f - v * g ∈ P) :
    ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometric».«mul_mem_sup_span» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mul_mem_sup_span_b3608818911e
