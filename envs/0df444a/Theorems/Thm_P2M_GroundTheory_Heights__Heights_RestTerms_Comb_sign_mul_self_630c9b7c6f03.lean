-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sign_mul_self_630c9b7c6f03
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sign_mul_self_630c9b7c6f03
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:01.985079+00:00
-- url     : https://prove2.me/theorems/e8642767-3601-57fd-8a14-94c8ce78d9bd
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb sign mul self 630c9b7c6f03: P2 M Ground Theory Heights  Heights Rest Terms Comb sign mul self 630c9b7c6f03
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb sign mul self 630c9b7c6f03 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb sign mul self 630c9b7c6f03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AltCoeff.lean#L48-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sign_mul_self_630c9b7c6f03 (σ : Perm (Fin m)) :
    ((Perm.sign σ : ℤ) : ℚ) * ((Perm.sign σ : ℤ) : ℚ) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«sign_mul_self» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sign_mul_self_630c9b7c6f03
