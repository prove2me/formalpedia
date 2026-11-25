-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_coeff_X_pow_mul_linear_pow_f3c190105c08
-- name    : P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_coeff_X_pow_mul_linear_pow_f3c190105c08
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:16.028798+00:00
-- url     : https://prove2.me/theorems/75a6ae01-14d1-4752-b712-9ff46a142e77
-- title:
--   P2 M Ground Theory Heights  Heights Generic Linear Trdeg coeff X pow mul linear pow f3c190105c08: P2 M Ground Theory Heights  Heights Generic Linear Trdeg coeff X pow mul linear pow f3c190105c08
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Linear Trdeg coeff X pow mul linear pow f3c190105c08 construction uses the P2 M Ground Theory Heights  Heights Generic Linear Trdeg coeff X pow mul linear pow f3c190105c08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PGenericLinearTrdeg.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg

theorem P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_coeff_X_pow_mul_linear_pow_f3c190105c08 {R : Type*} [CommRing R] (e c : R) (a b D : ℕ) (h : a + b ≤ D) :
    (Polynomial.X ^ a * (Polynomial.C e * Polynomial.X + Polynomial.C c) ^ b).coeff D =
      if a + b = D then e ^ b else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericLinearTrdeg».«coeff_X_pow_mul_linear_pow» := P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_coeff_X_pow_mul_linear_pow_f3c190105c08
