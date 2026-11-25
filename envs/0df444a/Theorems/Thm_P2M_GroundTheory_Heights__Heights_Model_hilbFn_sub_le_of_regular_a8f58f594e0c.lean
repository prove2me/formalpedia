-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_hilbFn_sub_le_of_regular_a8f58f594e0c
-- name    : P2M_GroundTheory_Heights__Heights_Model_hilbFn_sub_le_of_regular_a8f58f594e0c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:37.697334+00:00
-- url     : https://prove2.me/theorems/a3f72346-3be9-4192-aed8-451dc60231d4
-- title:
--   P2 M Ground Theory Heights  Heights Model hilb Fn sub le of regular a8f58f594e0c: P2 M Ground Theory Heights  Heights Model hilb Fn sub le of regular a8f58f594e0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model hilb Fn sub le of regular a8f58f594e0c construction uses the P2 M Ground Theory Heights  Heights Model hilb Fn sub le of regular a8f58f594e0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSectionNef.lean#L79-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSectionNef.lean#L79-L169

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

theorem P2M_GroundTheory_Heights__Heights_Model_hilbFn_sub_le_of_regular_a8f58f594e0c {P : Ideal (MRing ι F)} (hP : IsMultiProjPrime P) {b : K → ℤ}
    {f g : MRing ι F} (hs : IsRegularSection P b f g) :
    ∀ᶠ m in Filter.atTop, hilbFn P (m - b) ≤ hilbFn P m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«hilbFn_sub_le_of_regular» := P2M_GroundTheory_Heights__Heights_Model_hilbFn_sub_le_of_regular_a8f58f594e0c
