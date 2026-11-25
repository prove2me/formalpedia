-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:19.482223+00:00
-- url     : https://prove2.me/theorems/0893a65c-f94f-473c-b8de-a5a770607a7d
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Lower Bound hypotheses inhabited 32f5e648d58c: P2 M Ground Theory Heights  Heights Chow Height Lower Bound hypotheses inhabited 32f5e648d58c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Lower Bound hypotheses inhabited 32f5e648d58c construction uses the P2 M Ground Theory Heights  Heights Chow Height Lower Bound hypotheses inhabited 32f5e648d58c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L430-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L430-L445

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

theorem P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℚ) ∧
      Submodule.span (𝓞 ℚ) {(fun _ => 1 : Fin 1 → 𝓞 ℚ)} = ⊤ ∧
      (∀ s ∈ ({(fun _ => 1 : Fin 1 → 𝓞 ℚ)} : Set (Fin 1 → 𝓞 ℚ)), ∀ σ : ℚ →+* ℂ,
        ((ArchData.std ℚ 1).normAt σ).norm (fun j => σ (s j)) ≤ 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightLowerBound».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
