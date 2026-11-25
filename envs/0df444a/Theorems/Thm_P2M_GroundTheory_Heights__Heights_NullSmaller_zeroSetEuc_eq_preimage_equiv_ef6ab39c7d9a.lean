-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NullSmaller_zeroSetEuc_eq_preimage_equiv_ef6ab39c7d9a
-- name    : P2M_GroundTheory_Heights__Heights_NullSmaller_zeroSetEuc_eq_preimage_equiv_ef6ab39c7d9a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:00.03685+00:00
-- url     : https://prove2.me/theorems/6a6cd07f-ca44-4393-9aa9-019eaa3d7b2e
-- title:
--   P2 M Ground Theory Heights  Heights Null Smaller zero Set Euc eq preimage equiv ef6ab39c7d9a: P2 M Ground Theory Heights  Heights Null Smaller zero Set Euc eq preimage equiv ef6ab39c7d9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Null Smaller zero Set Euc eq preimage equiv ef6ab39c7d9a construction uses the P2 M Ground Theory Heights  Heights Null Smaller zero Set Euc eq preimage equiv ef6ab39c7d9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNullSmaller.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNullSmaller.lean#L14-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
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
open MvPolynomial MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NullSmaller_zeroSetEuc_eq_preimage_equiv_ef6ab39c7d9a {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NullSmaller».«zeroSetEuc_eq_preimage_equiv» := P2M_GroundTheory_Heights__Heights_NullSmaller_zeroSetEuc_eq_preimage_equiv_ef6ab39c7d9a
