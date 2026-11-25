-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eval_parYF_comp_d035261d91d5
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_eval_parYF_comp_d035261d91d5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:59.485328+00:00
-- url     : https://prove2.me/theorems/53977da4-3f58-49db-8a15-0ec7f56e525d
-- title:
--   P2 M Ground Theory Heights  Heights Vertical eval par YF comp d035261d91d5: P2 M Ground Theory Heights  Heights Vertical eval par YF comp d035261d91d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical eval par YF comp d035261d91d5 construction uses the P2 M Ground Theory Heights  Heights Vertical eval par YF comp d035261d91d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PParAlgIndep.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PParAlgIndep.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PParAlgIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Vertical_eval_parYF_comp_d035261d91d5 (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    (eval₂Hom (kToFrac K e n) (parYF K e n)).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (MvPolynomial (Par e n) K)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«eval_parYF_comp» := P2M_GroundTheory_Heights__Heights_Vertical_eval_parYF_comp_d035261d91d5
