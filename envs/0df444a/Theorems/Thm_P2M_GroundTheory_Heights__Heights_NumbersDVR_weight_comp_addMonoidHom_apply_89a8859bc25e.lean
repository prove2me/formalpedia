-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_apply_89a8859bc25e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_apply_89a8859bc25e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:02.580696+00:00
-- url     : https://prove2.me/theorems/8267f75d-15e8-48a6-b90f-851b12903750
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom apply 89a8859bc25e: P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom apply 89a8859bc25e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom apply 89a8859bc25e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom apply 89a8859bc25e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {σ : Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_apply_89a8859bc25e {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M)
    (f : M →+ M') (d : σ →₀ ℕ) : Finsupp.weight (fun v => f (w v)) d = f (Finsupp.weight w d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weight_comp_addMonoidHom_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_apply_89a8859bc25e
