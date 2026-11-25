-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_forms_mem_of_not_le_relevant_cc722a823041
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_forms_mem_of_not_le_relevant_cc722a823041
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:55.362482+00:00
-- url     : https://prove2.me/theorems/bcd29b6a-cccd-417c-b0e3-bf2df54aee50
-- title:
--   P2 M Ground Theory Heights  Heights Model exists forms mem of not le relevant cc722a823041: P2 M Ground Theory Heights  Heights Model exists forms mem of not le relevant cc722a823041
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists forms mem of not le relevant cc722a823041 construction uses the P2 M Ground Theory Heights  Heights Model exists forms mem of not le relevant cc722a823041 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSectionNef.lean#L21-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSectionNef.lean#L21-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSectionNef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open MvPolynomial NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type} [Field F]

theorem P2M_GroundTheory_Heights__Heights_Model_exists_forms_mem_of_not_le_relevant_cc722a823041 {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    (hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W → ¬ J ≤ W) :
    ∃ n : ℕ, ∀ m : K → ℕ, (∀ k, n * Fintype.card (ι k) < m k) →
      ∀ x : MRing ι F, IsMultiHomog x m → x ∈ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_forms_mem_of_not_le_relevant» := P2M_GroundTheory_Heights__Heights_Model_exists_forms_mem_of_not_le_relevant_cc722a823041
