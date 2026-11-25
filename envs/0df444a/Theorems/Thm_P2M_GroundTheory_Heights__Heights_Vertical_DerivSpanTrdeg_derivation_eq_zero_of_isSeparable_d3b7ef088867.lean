-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_DerivSpanTrdeg_derivation_eq_zero_of_isSeparable_d3b7ef088867
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_DerivSpanTrdeg_derivation_eq_zero_of_isSeparable_d3b7ef088867
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:06.511332+00:00
-- url     : https://prove2.me/theorems/74e6ce94-1781-4969-b561-db66fb0552ca
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Deriv Span Trdeg derivation eq zero of is Separable d3b7ef088867: P2 M Ground Theory Heights  Heights Vertical Deriv Span Trdeg derivation eq zero of is Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Deriv Span Trdeg derivation eq zero of is Separable d3b7ef088867 construction uses the P2 M Ground Theory Heights  Heights Vertical Deriv Span Trdeg derivation eq zero of is Separable d3b7ef088867 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PDerivSpanTrdeg.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PDerivSpanTrdeg.lean#L11-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsDerivSpanTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PDerivSpanTrdeg
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
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem P2M_GroundTheory_Heights__Heights_Vertical_DerivSpanTrdeg_derivation_eq_zero_of_isSeparable_d3b7ef088867 {k K M : Type*} [Field k] [Field K]
    [Algebra k K] [AddCommGroup M] [Module K M] [Module k M] [IsScalarTower k K M] (s : Set K)
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] (D : Derivation k K M)
    (hs : ∀ x ∈ s, D x = 0) : D = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«DerivSpanTrdeg».«derivation_eq_zero_of_isSeparable» := P2M_GroundTheory_Heights__Heights_Vertical_DerivSpanTrdeg_derivation_eq_zero_of_isSeparable_d3b7ef088867
