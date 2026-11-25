-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_hypotheses_inhabited_0ebf35365ba4
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_hypotheses_inhabited_0ebf35365ba4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:16.160636+00:00
-- url     : https://prove2.me/theorems/c038d207-8d47-51a1-8189-95aaee047799
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Homog hypotheses inhabited 0ebf35365ba4: P2 M Ground Theory Heights  Heights Minimal Prime Homog hypotheses inhabited 0ebf35365ba4
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Homog hypotheses inhabited 0ebf35365ba4 construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Homog hypotheses inhabited 0ebf35365ba4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L128-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinear_hypotheses_inhabited_1fdf021d66be

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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_hypotheses_inhabited_0ebf35365ba4 :
    IsHomogIdeal (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimeHomog».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_hypotheses_inhabited_0ebf35365ba4
