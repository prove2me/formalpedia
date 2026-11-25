-- Prove2me | Theorems.Thm_P2M_UpperTheory_Lit_Mix_ind__at_8cfc4edaf794
-- name    : P2M_UpperTheory_Lit_Mix_ind__at_8cfc4edaf794
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:06.922113+00:00
-- url     : https://prove2.me/theorems/2c832a3a-2148-55be-bd43-e21ff11f6374
-- title:
--   P2 M Upper Theory Lit Mix ind  at 8cfc4edaf794: P2 M Upper Theory Lit Mix ind  at 8cfc4edaf794
-- statement:
--   The P2 M Upper Theory Lit Mix ind  at 8cfc4edaf794 construction uses the P2 M Upper Theory Lit Mix ind  at 8cfc4edaf794 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MultiAt.lean#L23-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MultiAt.lean#L23-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Definitions.Def_Development_AutomorphicArithmetic_ThetaCorrespondence_GeneralLinearGroups_MultiAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr ValuativeRel Matrix
open scoped TensorProduct
open UpperTheory UpperTheory.Lit UpperTheory.Lit.Mix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem P2M_UpperTheory_Lit_Mix_ind__at_8cfc4edaf794 (H : TwoAt k) (e : a ⊕ b ≃ n)
    {π₁ : Representation ℂ (GL a k) V} {π₂ : Representation ℂ (GL b k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ e (extTensor π₁ π₂)).IsIrreducible := by sorry

alias «UpperTheory».«Lit».«Mix».«ind₂_at» := P2M_UpperTheory_Lit_Mix_ind__at_8cfc4edaf794
