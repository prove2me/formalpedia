-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_colon_ca90d2ed2e72
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_colon_ca90d2ed2e72
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:01.782779+00:00
-- url     : https://prove2.me/theorems/48516951-b85d-43c2-8235-306a7b3f3345
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog colon ca90d2ed2e72: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog colon ca90d2ed2e72
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog colon ca90d2ed2e72 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog colon ca90d2ed2e72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L135-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L135-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_colon_ca90d2ed2e72 {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) {s : MRing ι F}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (J.colon (Ideal.span {s})) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«multiHomog_colon» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_colon_ca90d2ed2e72
