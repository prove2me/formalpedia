-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_exists_unit_e6847bea0649
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_exists_unit_e6847bea0649
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:24.703471+00:00
-- url     : https://prove2.me/theorems/01d5122c-86e7-46e7-9ed2-c5ae7b622afc
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms exists unit e6847bea0649: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms exists unit e6847bea0649
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms exists unit e6847bea0649 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Isometric Forms exists unit e6847bea0649 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L122-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean#L122-L168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_exists_unit_e7832c878c51

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
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_exists_unit_e6847bea0649 {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι} (hBP : IsBasePtFree P g)
    (j : ∀ k, ι₂ k) (a : K₂ → ℤ) {W : Ideal (MRing (Sum.elim ι ι₂))} (hW : W.IsPrime)
    (hΓW : graphIdeal P g ≤ W) (hrel : IsRelevant W) :
    ∃ u v, u ∉ W ∧ v ∉ W ∧ u * num g j a - v * den g j a ∈ graphIdeal P g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphIsometricForms».«exists_unit» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_exists_unit_e6847bea0649
