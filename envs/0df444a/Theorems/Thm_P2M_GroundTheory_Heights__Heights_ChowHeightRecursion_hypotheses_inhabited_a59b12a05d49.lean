-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:24.640389+00:00
-- url     : https://prove2.me/theorems/9468d7ce-6a5b-40eb-b551-38b76417cb81
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Recursion hypotheses inhabited a59b12a05d49: P2 M Ground Theory Heights  Heights Chow Height Recursion hypotheses inhabited a59b12a05d49
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Recursion hypotheses inhabited a59b12a05d49 construction uses the P2 M Ground Theory Heights  Heights Chow Height Recursion hypotheses inhabited a59b12a05d49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L421-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L421-L428

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
open MvPolynomial MeasureTheory NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49 :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℚ) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightRecursion».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
