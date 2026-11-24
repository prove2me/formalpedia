-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphChangeOfModel_exists_form_not_mem_96d674878670
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphChangeOfModel_exists_form_not_mem_96d674878670
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:30.527184+00:00
-- url     : https://prove2.me/theorems/70f34a15-536d-4693-a986-b1ddf9068ea1
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Change Of Model exists form not mem 96d674878670: P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Change Of Model exists form not mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Change Of Model exists form not mem 96d674878670 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graph Change Of Model exists form not mem 96d674878670 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphChangeOfModel.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphChangeOfModel.lean#L21-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} {ι₂ : K₂ → Type}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphChangeOfModel_exists_form_not_mem_96d674878670 {P : Ideal (MRing ι)} {d : ℕ} {g : (Σ k, ι₂ k) → MRing ι} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P g) : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GraphChangeOfModel».«exists_form_not_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphChangeOfModel_exists_form_not_mem_96d674878670
