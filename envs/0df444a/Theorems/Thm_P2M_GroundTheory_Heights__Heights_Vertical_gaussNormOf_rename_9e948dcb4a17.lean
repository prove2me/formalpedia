-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_gaussNormOf_rename_9e948dcb4a17
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_gaussNormOf_rename_9e948dcb4a17
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:08.227847+00:00
-- url     : https://prove2.me/theorems/7f034c59-8bd8-4374-b9ba-a16b99879855
-- title:
--   P2 M Ground Theory Heights  Heights Vertical gauss Norm Of rename 9e948dcb4a17: P2 M Ground Theory Heights  Heights Vertical gauss Norm Of rename 9e948dcb4a17
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical gauss Norm Of rename 9e948dcb4a17 construction uses the P2 M Ground Theory Heights  Heights Vertical gauss Norm Of rename 9e948dcb4a17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussEq.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussEq.lean#L12-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussEq
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_gaussNormOf_rename_9e948dcb4a17 {R : Type*} [CommRing R] (w : AbsoluteValue R ℝ) {σ τ : Type*}
    {f : σ → τ} (hf : Function.Injective f) (x : MvPolynomial σ R) :
    gaussNormOf w (rename f x) = gaussNormOf w x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«gaussNormOf_rename» := P2M_GroundTheory_Heights__Heights_Vertical_gaussNormOf_rename_9e948dcb4a17
