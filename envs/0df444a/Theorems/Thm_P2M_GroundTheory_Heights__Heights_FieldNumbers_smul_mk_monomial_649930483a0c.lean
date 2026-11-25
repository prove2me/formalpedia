-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_smul_mk_monomial_649930483a0c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_smul_mk_monomial_649930483a0c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:00.504625+00:00
-- url     : https://prove2.me/theorems/603e72e6-ae6f-43ab-a8e0-a332bc5e2941
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers smul mk monomial 649930483a0c: P2 M Ground Theory Heights  Heights Field Numbers smul mk monomial 649930483a0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers smul mk monomial 649930483a0c construction uses the P2 M Ground Theory Heights  Heights Field Numbers smul mk monomial 649930483a0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L180-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBaseChange.lean#L180-L184

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_smul_mk_monomial_649930483a0c (E : Type*) [Field E] (J : Ideal (MRing ι E)) (d : (Σ k, ι k) →₀ ℕ)
    (c : E) : c • Ideal.Quotient.mk J (monomial d (1 : E)) = Ideal.Quotient.mk J (monomial d c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«smul_mk_monomial» := P2M_GroundTheory_Heights__Heights_FieldNumbers_smul_mk_monomial_649930483a0c
