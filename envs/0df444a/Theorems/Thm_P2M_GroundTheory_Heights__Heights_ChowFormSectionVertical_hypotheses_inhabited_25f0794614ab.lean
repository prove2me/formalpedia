-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:17.59993+00:00
-- url     : https://prove2.me/theorems/01267bd1-3dfd-4f2e-9e5c-5d605eb55995
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Section Vertical hypotheses inhabited 25f0794614ab: P2 M Ground Theory Heights  Heights Chow Form Section Vertical hypotheses inhabited 25f0794614ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Section Vertical hypotheses inhabited 25f0794614ab construction uses the P2 M Ground Theory Heights  Heights Chow Form Section Vertical hypotheses inhabited 25f0794614ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L383-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L383-L389

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

theorem P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormSectionVertical».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
