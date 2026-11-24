-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_pi_quot_smul_top_69b4b0f38899
-- name    : P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_pi_quot_smul_top_69b4b0f38899
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:37.721826+00:00
-- url     : https://prove2.me/theorems/e045f89a-fd04-46ea-9aba-d98688f5b06a
-- title:
--   P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length pi quot smul top 69b4b0f38899: P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length pi quot smul
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length pi quot smul top 69b4b0f38899 construction uses the P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length pi quot smul top 69b4b0f38899 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PTorsionFreeQuotientLength.lean#L14-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PTorsionFreeQuotientLength.lean#L14-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
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
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_pi_quot_smul_top_69b4b0f38899 (t : ℕ) (a : R) :
    Module.length R ((Fin t → R) ⧸ (a • ⊤ : Submodule R (Fin t → R))) =
      t * Module.length R (R ⧸ Ideal.span {a}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«TorsionFreeQuotientLength».«length_pi_quot_smul_top» := P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_pi_quot_smul_top_69b4b0f38899
