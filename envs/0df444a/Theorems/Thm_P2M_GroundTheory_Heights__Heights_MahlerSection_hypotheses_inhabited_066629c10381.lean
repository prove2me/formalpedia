-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
-- name    : P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:23.781734+00:00
-- url     : https://prove2.me/theorems/2a0606c4-ea74-4fe4-b902-06c48573b0ac
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Section hypotheses inhabited 066629c10381: P2 M Ground Theory Heights  Heights Mahler Section hypotheses inhabited 066629c10381
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Section hypotheses inhabited 066629c10381 construction uses the P2 M Ground Theory Heights  Heights Mahler Section hypotheses inhabited 066629c10381 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L395-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L395-L411

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

theorem P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381 :
    (∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support, IsProjPrime W) ∧
      IsChowFormCycle (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) ∧
      (∀ W ∈ (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1).support,
        linForm (fun _ => (1 : ℂ)) ∉ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerSection».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
